% Nested quantifiers
fof(axiom1, axiom, ![X]: (?[Y]: loves(X,Y))).
fof(axiom2, axiom, ![X,Y]: (loves(X,Y) => happy(X))).
fof(goal, conjecture, ![Z]: happy(Z)).
