% This file's own directory (tests/fixtures/tptp_include/problems/) has no
% Axioms/ subdirectory at all -- 'Axioms/animals.ax' resolves ONLY through a
% search_paths root pointed at tests/fixtures/tptp_include/library/, never
% relative to this file. See test_include_resolves_only_via_search_paths_root
% in tests/test_tptp_include.py.
include('Axioms/animals.ax').
fof(goal, conjecture, animal(rex)).
