%------------------------------------------------------------------------------
% File     : simple_prop.p
% Domain   : Propositional Logic
% Problem  : Modus Ponens - Simplest inference
% English  : Given P and P => Q, prove Q
%------------------------------------------------------------------------------

% Axioms (facts in KB)
fof(fact_p, axiom, p).
fof(fact_impl, axiom, p => q).

% Goal (conjecture to prove)
fof(goal, conjecture, q).

%------------------------------------------------------------------------------
