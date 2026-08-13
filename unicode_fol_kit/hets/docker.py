r"""Docker lifecycle + server discovery for a local HETS instance.

This module owns everything about *getting to a running HETS REST server* —
:mod:`~unicode_fol_kit.hets.client` owns everything about *talking to one once
you have its URL*. That split is deliberate: :class:`HetsClient` never shells
out or touches Docker, so it works identically against a container this kit
started, a container someone else started, or a bare-metal HETS install behind
a reverse proxy — anything answering the REST API on some ``http://host:port``.

Why Docker at all
------------------
HETS (the Heterogeneous Tool Set, https://github.com/spechub/Hets) is a large
Haskell program with a GPL-family license and a build that is realistically
only reproducible via the ``spechub2/hets`` Docker image (a GHC toolchain,
dozens of pinned library versions, and the bundled provers). Two ways exist to
use it from Python:

1. **In-process bindings** (the ``hets`` PyPI/``spechub`` Python API some
   installs expose) — link this process directly against a GPL Haskell
   library, AND it is only buildable/available on Linux with a working GHC
   toolchain. Neither holds for this kit's primary dev platform (Windows) or
   its license posture (MIT).
2. **REST against a Docker container** — the route this module takes. HETS
   already ships an HTTP server (``hets-server``) inside the official image;
   this kit only ever speaks HTTP to it. That is a real process/network
   boundary, not a linking relationship — this kit's own code never imports,
   links, or bundles any GPL component, and the container can be swapped for
   any other HETS deployment (a shared server, a CI sidecar) without touching
   a line of Python here. :class:`HetsContainer` is a convenience for
   *local* use (spin one up, talk to it, tear it down); nothing about the
   client depends on this kit having started the container it talks to.

Container image quirks (spechub2/hets:latest, HETS 0.108.0 — verified live)
-----------------------------------------------------------------------------
Not every prover this image advertises via ``GET /provers/<iri>`` actually
works when invoked via ``POST /prove/<iri>``:

* ``eprover`` — the wrapper script in this image is broken: its
  ``prover_output`` ends with ``/bin/sh: 1: SZS: not found`` and the goal
  stays ``"Open\n"`` no matter the input. Do not use it.
* ``Vampire`` — returns ``"Open\n"`` with empty ``prover_output`` for every
  goal tried; effectively non-functional in this image.
* ``SPASS`` (via the ``CASL2TPTP_FOF`` translation), ``darwin``, and
  ``darwin-non-fd`` (the finite-model DISPROVER — the one that actually
  returns ``"Disproved\n"`` for a non-theorem, since plain ``darwin`` is a
  model finder tuned for SATISFIABLE/proof, not for certifying
  unprovability) all work and are what :mod:`~unicode_fol_kit.hets.client`'s
  docstring examples and this kit's live tests use.

**``"Open\n"`` means UNKNOWN, never REFUTED.** A prover reporting ``Open`` has
not found a proof within its budget; it has not certified the goal false.
Silently treating a broken/timed-out prover's ``Open`` as a disproof would be
exactly the "silent downgrade" failure mode this kit's ``atp.protocol``
module is built to prevent (see its module docstring) — callers of
:mod:`~unicode_fol_kit.hets.client` must keep that distinction themselves;
this module and the client only ever pass the reasoner's own ``result``
string through unmodified.

Lifecycle
---------
:class:`HetsContainer` runs, health-polls, and stops one
``spechub2/hets:latest`` container. :func:`discover_hets_url` is the entry
point most callers want: it never silently proceeds without a real server —
an env var pointing nowhere, a missing ``docker`` binary, a stopped Docker
daemon, or an unpullable image all raise :class:`BackendUnavailable` with a
concrete next step, mirroring
:mod:`unicode_fol_kit.hol.isabelle_runner`'s "never guess, always say how to
fix it" discovery contract. :func:`hets_available` is the cheap, non-raising
predicate that test files gate on (the ``isabelle_available()`` role for this
backend).
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import time
import urllib.error
import urllib.request
import uuid
from typing import Optional, Tuple

from ..atp.protocol import BackendUnavailable

__all__ = [
    "HETS_IMAGE", "HetsContainer", "discover_hets_url", "hets_available",
]

HETS_IMAGE = "spechub2/hets:latest"

_DEFAULT_PORT = 8000
_VERSION_PATH = "/version"
_HEALTH_TIMEOUT = 2.0          # per-probe socket timeout, not the overall budget
_POLL_INTERVAL = 0.5

# docker CLI stderr signatures. Deliberately permissive (a few alternatives
# per scenario) since the exact wording differs across Docker Desktop /
# Engine versions and Windows named-pipe vs. Linux unix-socket transports —
# a missed pattern degrades to the generic "docker run failed" branch, which
# is still a loud BackendUnavailable, just a less specific one.
_DAEMON_DOWN_RE = re.compile(
    r"cannot connect to the docker daemon|"
    r"daemon is not running|"
    r"error during connect|"
    r"pipe/dockerdesktoplinuxengine|"
    r"dial (?:unix|tcp).*(?:no such file|connection refused|actively refused)",
    re.I,
)
_IMAGE_MISSING_RE = re.compile(
    r"pull access denied|"
    r"repository does not exist|"
    r"manifest (?:unknown|for .* not found)|"
    r"no such host|"
    r"failed to resolve reference|"
    r"error response from daemon: get ",
    re.I,
)
_PORT_BUSY_RE = re.compile(
    r"port is already allocated|"
    r"bind for [\d.:]+ failed|"
    r"address already in use",
    re.I,
)


def _probe_health(url: str, timeout: float = _HEALTH_TIMEOUT) -> bool:
    """``True`` iff ``GET <url>/version`` answers HTTP 200 within ``timeout``.

    The single primitive both :func:`discover_hets_url` and
    :class:`HetsContainer` poll on. Any failure (connection refused, DNS,
    timeout, non-200) is treated as "not healthy yet" — this is a liveness
    probe, not a diagnostic, so it swallows everything and returns ``bool``.
    """
    try:
        with urllib.request.urlopen(
            url.rstrip("/") + _VERSION_PATH, timeout=timeout
        ) as resp:
            return 200 <= resp.status < 300
    except (urllib.error.URLError, OSError, ValueError):
        return False


class HetsContainer:
    """Context manager around one ``docker run`` of :data:`HETS_IMAGE`.

    Usage::

        with HetsContainer(port=8001) as hc:
            client = HetsClient(hc.url)
            ...
        # container stopped on exit, even if the body raised

    ``start()`` and ``__enter__`` are equivalent (``__enter__`` just calls
    ``start()`` and returns ``self``) — both are provided so a caller that
    wants to hold onto the object before entering a ``with`` block (e.g. to
    pass it around) can call ``start()`` directly.
    """

    def __init__(self, *, port: int = _DEFAULT_PORT, name: Optional[str] = None,
                 health_timeout: float = 60.0):
        self.port = port
        self.name = name or f"ufk-hets-{uuid.uuid4().hex[:8]}"
        self.health_timeout = health_timeout
        self.url = f"http://localhost:{port}"
        self._started = False

    def start(self) -> "HetsContainer":
        """Run the container and block until ``GET /version`` answers.

        Raises:
            BackendUnavailable: no ``docker`` binary on PATH; the Docker
                daemon is not running; the image is absent locally and could
                not be pulled; ``docker run`` failed for any other reason;
                or the container started but never became healthy within
                ``health_timeout`` seconds (the container is stopped first,
                so a failed start never leaks a running container).
        """
        docker_bin = shutil.which("docker")
        if docker_bin is None:
            raise BackendUnavailable(
                "hets: no `docker` binary found on PATH. Install Docker Desktop "
                "(https://www.docker.com/products/docker-desktop/) and ensure "
                "`docker` is on PATH, or set $UFK_HETS_URL to a running HETS "
                "server instead of asking this kit to manage a container."
            )

        cmd = [docker_bin, "run", "-d", "--rm", "-p", f"{self.port}:8000",
               "--name", self.name, HETS_IMAGE]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        if proc.returncode != 0:
            stderr = (proc.stderr or "").strip()
            if _DAEMON_DOWN_RE.search(stderr):
                raise BackendUnavailable(
                    "hets: the Docker daemon is not running. Start Docker "
                    "Desktop (or `sudo systemctl start docker` on Linux), or "
                    "set $UFK_HETS_URL to a running HETS server.\n"
                    f"docker stderr: {stderr}"
                )
            if _IMAGE_MISSING_RE.search(stderr):
                raise BackendUnavailable(
                    f"hets: image {HETS_IMAGE!r} is not present locally and "
                    f"could not be pulled automatically. Run "
                    f"`docker pull {HETS_IMAGE}` (needs network access), or "
                    "set $UFK_HETS_URL to a running HETS server.\n"
                    f"docker stderr: {stderr}"
                )
            if _PORT_BUSY_RE.search(stderr):
                # The single most likely real failure with a fixed default
                # port (review-flagged): something — often a PREVIOUS hets
                # container — already owns it.
                raise BackendUnavailable(
                    f"hets: port {self.port} is already in use — likely an "
                    "already-running HETS container (then just use it: "
                    f"discover_hets_url() finds http://localhost:{self.port}) "
                    f"or another service (then pick HetsContainer(port=...) "
                    "differently).\n"
                    f"docker stderr: {stderr}"
                )
            raise BackendUnavailable(
                f"hets: `docker run` failed (exit {proc.returncode}). Check "
                f"`docker info` for daemon health, or set $UFK_HETS_URL to a "
                f"running HETS server instead.\ndocker stderr: {stderr}"
            )

        self._started = True
        deadline = time.monotonic() + self.health_timeout
        while time.monotonic() < deadline:
            if _probe_health(self.url):
                return self
            time.sleep(_POLL_INTERVAL)

        # Started but never answered — do not leak a running-but-useless
        # container onto the caller's machine.
        self.stop()
        raise BackendUnavailable(
            f"hets: container {self.name!r} (image {HETS_IMAGE}) was started "
            f"but did not answer GET {self.url}{_VERSION_PATH} within "
            f"{self.health_timeout}s. Inspect it with `docker logs {self.name}` "
            "before it was stopped, or raise health_timeout."
        )

    def stop(self) -> None:
        """Stop the container (no-op if never started or already stopped).

        Uses ``docker stop`` rather than ``docker kill`` — the container was
        started with ``--rm``, so a stop also removes it. Failures here are
        swallowed (best-effort cleanup): raising out of ``stop()``/``__exit__``
        would mask whatever exception the ``with`` body itself raised.
        """
        if not self._started:
            return
        docker_bin = shutil.which("docker") or "docker"
        subprocess.run([docker_bin, "stop", self.name], capture_output=True, text=True)
        self._started = False

    def __enter__(self) -> "HetsContainer":
        return self.start()

    def __exit__(self, exc_type, exc, tb) -> bool:
        self.stop()
        return False


def discover_hets_url(
    *, start_container: bool = False, port: int = _DEFAULT_PORT,
    health_timeout: float = 60.0,
) -> Tuple[str, Optional[HetsContainer]]:
    """Find a reachable HETS server URL, in order of precedence.

    1. ``$UFK_HETS_URL`` — if set to a NON-EMPTY value, it is health-checked
       (never trusted blind); an unhealthy value raises
       :class:`BackendUnavailable` naming the broken env var rather than
       silently falling through to the next option (a caller who
       deliberately pointed at a specific server wants to know THAT server
       is down, not get a different one back). An EMPTY string is treated
       exactly like an unset variable — deliberate, so
       ``UFK_HETS_URL=$SOME_UNSET_CI_VAR`` degrades to normal discovery
       instead of a guaranteed error about the empty URL.
    2. ``http://localhost:<port>`` — checked whether or not this kit started
       it (covers a container someone already has running, or a non-Docker
       local install).
    3. If ``start_container=True``: start a fresh :class:`HetsContainer` on
       ``port`` and return its URL.
    4. Otherwise: raise :class:`BackendUnavailable` listing every option
       tried and how to fix each one. Never silently returns a URL nobody
       verified answers.

    Returns:
        ``(url, container)`` — ``container`` is the started
        :class:`HetsContainer` when this call started one (case 3, so the
        caller can ``container.stop()`` when done), else ``None`` (cases 1-2:
        an already-running server this call does not own and must not stop).

    Raises:
        BackendUnavailable: nothing reachable, per the precedence above.
    """
    env_url = os.environ.get("UFK_HETS_URL")
    if env_url:
        if _probe_health(env_url):
            return env_url, None
        raise BackendUnavailable(
            f"hets: $UFK_HETS_URL={env_url!r} is set but did not answer "
            f"GET {env_url.rstrip('/')}{_VERSION_PATH} — point it at a live "
            "HETS server, or unset it to fall back to localhost/auto-start."
        )

    local_url = f"http://localhost:{port}"
    if _probe_health(local_url):
        return local_url, None

    if start_container:
        container = HetsContainer(port=port, health_timeout=health_timeout).start()
        return container.url, container

    raise BackendUnavailable(
        "hets: no server discovered. Tried, in order:\n"
        "  1. $UFK_HETS_URL — not set\n"
        f"  2. {local_url}{_VERSION_PATH} — no response\n"
        "Fix one of:\n"
        "  - set $UFK_HETS_URL to a running HETS server\n"
        f"  - start one yourself: docker run -d --rm -p {port}:8000 {HETS_IMAGE}\n"
        "  - call discover_hets_url(start_container=True) to have this kit "
        "start and own a container (requires Docker Desktop / a running "
        "daemon; install from https://www.docker.com/products/docker-desktop/)"
    )


def hets_available(*, port: int = _DEFAULT_PORT) -> bool:
    """Cheap, non-raising predicate: is a HETS server reachable right now?

    Mirrors :func:`unicode_fol_kit.hol.isabelle_runner.isabelle_available` —
    live test files gate (``skipif``) on THIS, never on a bare env-var
    presence check, so the skip is accurate whether the server is reached
    via ``$UFK_HETS_URL`` or an already-running localhost container. Never
    starts a container (calls :func:`discover_hets_url` with
    ``start_container=False``), so probing a test's availability never has
    the side effect of spinning up Docker.
    """
    try:
        discover_hets_url(start_container=False, port=port)
        return True
    except BackendUnavailable:
        return False
