%--------------------------------------------------------------------------
% File     : distinct_not_related : unicode-logic-kit fixture in QMLTP v1.1 syntax
% Domain   : Syntactic (modal)
% Problem  : Distinct objects are necessarily unrelated (a non-theorem).
% English  : any two distinct objects necessarily do not stand in r
%
% Source   : unicode-logic-kit
%
% Status   :      varying      cumulative   constant
%             K   Non-Theorem  Non-Theorem  Non-Theorem
%             D   Non-Theorem  Non-Theorem  Non-Theorem
%             T   Non-Theorem  Non-Theorem  Non-Theorem
%             S4  Non-Theorem  Non-Theorem  Non-Theorem
%             S5  Non-Theorem  Non-Theorem  Non-Theorem
%
% Comments : Written for unicode-logic-kit's test suite, not taken from the
%            QMLTP library. Exercises equality plus a binary user
%            predicate. Status derived by hand: r is uninterpreted, so a
%            model with two distinct objects related by r at the world
%            itself (reflexive and symmetric, hence in every frame class)
%            falsifies it under every domain condition.
%--------------------------------------------------------------------------

qmf(con,conjecture,
( ! [X] : ( ! [Y] : ( ( ~ ( X = Y ) ) => ( #box : ( ~ ( r(X,Y) ) ) ) ) ) )).
