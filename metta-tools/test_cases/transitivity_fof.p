% Transitivity of a binary relation
% If R is transitive and R(a,b) and R(b,c), then R(a,c)

fof(transitivity, axiom,
    ![X,Y,Z]: ((r(X,Y) & r(Y,Z)) => r(X,Z))).

fof(r_ab, axiom,
    r(a,b)).

fof(r_bc, axiom,
    r(b,c)).

fof(r_ac, conjecture,
    r(a,c)).
