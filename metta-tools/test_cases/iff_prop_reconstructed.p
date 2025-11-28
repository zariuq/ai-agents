%-----------------------------------------------------------------------------
% File     : iff_prop.p
% Domain   : Propositional Logic
% Problem  : Equivalence (biconditional)
% English  : Given p <=> q and p, prove q
%-----------------------------------------------------------------------------

fof(equivalence,axiom,
    ( p <=> q ) ).

fof(fact_p,axiom,
    p ).

fof(goal,conjecture,
    q ).

%-----------------------------------------------------------------------------
