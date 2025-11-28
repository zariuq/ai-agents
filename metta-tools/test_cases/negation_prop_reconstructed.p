%-----------------------------------------------------------------------------
% File     : negation_prop.p
% Domain   : Propositional Logic
% Problem  : Double negation elimination
% English  : Prove p from ~ ~ p
%-----------------------------------------------------------------------------

fof(double_neg,axiom,
    ~ ~ p ).

fof(goal,conjecture,
    p ).

%-----------------------------------------------------------------------------
