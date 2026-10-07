%--------------------------------------------------------------------------
% File     : box_all_to_dia_all : unicode-logic-kit fixture in QMLTP v1.1 syntax
% Domain   : Syntactic (modal)
% Problem  : Every x necessarily f, so possibly every x f.
% English  : if for every x necessarily f(x), then possibly for every x
%            f(x)
%
% Refs     : [FM98] M. Fitting, R. L. Mendelsohn. First-Order Modal Logic.
%            Kluwer, 1998.
% Source   : [FM98]
%
% Status   :      varying      cumulative   constant
%             K   Non-Theorem  Non-Theorem  Non-Theorem
%             D   Non-Theorem  Non-Theorem  Theorem
%             T   Theorem      Theorem      Theorem
%             S4  Theorem      Theorem      Theorem
%             S5  Theorem      Theorem      Theorem
%
% Comments : Written for unicode-logic-kit's test suite, not taken from the
%            QMLTP library. Status derived by hand: in K a dead-end world
%            makes the antecedent true and every diamond false. In D some
%            successor v exists; over constant domains every x has f at v,
%            but a varying or growing domain may give v an object without
%            f. In T, S4 and S5 the world itself is a successor, and the
%            antecedent makes f hold there of every local object.
%--------------------------------------------------------------------------

qmf(con,conjecture,
( ( ! [X] : ( #box : ( f(X) ) ) ) => ( #dia : ( ! [X] : ( f(X) ) ) ) )).
