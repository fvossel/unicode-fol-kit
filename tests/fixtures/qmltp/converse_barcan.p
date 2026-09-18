%--------------------------------------------------------------------------
% File     : converse_barcan : unicode-fol-kit fixture in QMLTP v1.1 syntax
% Domain   : Syntactic (modal)
% Problem  : Converse Barcan scheme instance.
% English  : if necessarily for every x f(x), then for every x
%            necessarily f(x)
%
% Refs     : [Brc46] R. C. Barcan. A functional calculus of first order
%            based on strict implication. Journal of Symbolic Logic
%            11:1-16, 1946.
% Source   : [Brc46]
%
% Status   :      varying      cumulative   constant
%             K   Non-Theorem  Theorem      Theorem
%             D   Non-Theorem  Theorem      Theorem
%             T   Non-Theorem  Theorem      Theorem
%             S4  Non-Theorem  Theorem      Theorem
%             S5  Non-Theorem  Theorem      Theorem
%
% Comments : Written for unicode-fol-kit's test suite, not taken from the
%            QMLTP library. Status derived by hand: the converse Barcan
%            scheme is exactly what a non-shrinking (cumulative) domain
%            validates, in every frame; a varying domain may drop an
%            object at the successor, where f then need not hold of it.
%--------------------------------------------------------------------------

qmf(con,conjecture,
( ( #box : ( ! [X] : ( f(X) ) ) ) => ( ! [X] : ( #box : ( f(X) ) ) ) )).
