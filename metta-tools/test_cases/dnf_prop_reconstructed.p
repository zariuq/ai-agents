%-----------------------------------------------------------------------------
% File     : dnf_prop.p
% Domain   : Propositional Logic
% Problem  : Disjunctive Normal Form example
% English  : Prove (p & q) | (p & r) from p & (q | r)
%-----------------------------------------------------------------------------

fof(premise,axiom,
    ( p & ( q | r ) ) ).

fof(goal,conjecture,
    ( ( p & q ) | ( p & r ) ) ).

%-----------------------------------------------------------------------------
