%------------------------------------------------------------------------------
% File     : negation_prop.p
% Domain   : Propositional Logic
% Problem  : Double negation elimination
% English  : Prove p from ~ ~ p
%------------------------------------------------------------------------------

% Axiom: double negation
fof(double_neg, axiom, ~ ~ p).

% Goal: eliminate double negation
fof(goal, conjecture, p).

%------------------------------------------------------------------------------
