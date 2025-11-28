% Simple propositional test problem for binary resolution
% Problem: Basic resolution test
%  (p | q) & (~p | r) => (q | r)

fof(clause1, axiom, p | q).
fof(clause2, axiom, ~p | r).
fof(goal, conjecture, q | r).
