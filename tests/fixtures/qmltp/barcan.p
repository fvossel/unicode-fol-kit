%--------------------------------------------------------------------------
% File     : barcan : unicode-fol-kit fixture in QMLTP v1.1 syntax
% Domain   : Syntactic (modal)
% Problem  : Barcan scheme instance.
% English  : if for every x necessarily f(x), then necessarily for every
%            x f(x)
%
% Refs     : [Brc46] R. C. Barcan. A functional calculus of first order
%            based on strict implication. Journal of Symbolic Logic
%            11:1-16, 1946.
% Source   : [Brc46]
%
% Status   :      varying      cumulative   constant
%             K   Non-Theorem  Non-Theorem  Theorem
%             D   Non-Theorem  Non-Theorem  Theorem
%             T   Non-Theorem  Non-Theorem  Theorem
%             S4  Non-Theorem  Non-Theorem  Theorem
%             S5  Non-Theorem  Theorem      Theorem
%
% Comments : Written for unicode-fol-kit's test suite, not taken from the
%            QMLTP library. Status derived by hand: over constant domains
%            the scheme holds in every frame; a varying domain, or a
%            growing one reached along a non-symmetric edge, can add an
%            object at the successor where f fails. S5's symmetry forces a
%            cumulative domain to be constant within a cluster, which is
%            why that one cell is a Theorem.
%--------------------------------------------------------------------------

qmf(con,conjecture,
( ( ! [X] : ( #box : ( f(X) ) ) ) => ( #box : ( ! [X] : ( f(X) ) ) ) )).
