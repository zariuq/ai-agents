% Simple propositional test for resolution
% Should derive empty clause (UNSAT)

fof(clause1, axiom, p | q).
fof(clause2, axiom, ~p | q).
fof(clause3, axiom, p | ~q).
fof(clause4, axiom, ~p | ~q).

% These four clauses are contradictory
% Resolution should find empty clause
