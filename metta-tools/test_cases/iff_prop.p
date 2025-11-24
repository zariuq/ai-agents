%------------------------------------------------------------------------------
% File     : iff_prop.p
% Domain   : Propositional Logic
% Problem  : Equivalence (biconditional)
% English  : Given p <=> q and p, prove q
%------------------------------------------------------------------------------

% Axioms
fof(equivalence, axiom, p <=> q).
fof(fact_p, axiom, p).

% Goal
fof(goal, conjecture, q).

%------------------------------------------------------------------------------
