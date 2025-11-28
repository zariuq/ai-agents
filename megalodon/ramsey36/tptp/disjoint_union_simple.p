% Simpler: prove by induction on second argument
% For all M: if equip(M,A), then for all N: if equip(N,B) & disjoint(A,B), then equip(M+N, A union B)

fof(equipDef, axiom, ![X,Y]: (equip(X,Y) <=> bijExists(X,Y))).
fof(equipRef, axiom, ![X]: equip(X,X)).
fof(equipSym, axiom, ![X,Y]: (equip(X,Y) => equip(Y,X))).
fof(equipTra, axiom, ![X,Y,Z]: (equip(X,Y) & equip(Y,Z) => equip(X,Z))).

fof(binunionI1, axiom, ![X,Y,Z]: (elt(Z,X) => elt(Z,binunion(X,Y)))).
fof(binunionI2, axiom, ![X,Y,Z]: (elt(Z,Y) => elt(Z,binunion(X,Y)))).
fof(binunionE, axiom, ![X,Y,Z]: (elt(Z,binunion(X,Y)) => (elt(Z,X) | elt(Z,Y)))).

fof(singI, axiom, ![X]: elt(X, sing(X))).
fof(singE, axiom, ![X,Y]: (elt(Y, sing(X)) => Y = X)).

fof(disjointDef, axiom, ![A,B]: (disjoint(A,B) <=> ![X]: ~(elt(X,A) & elt(X,B)))).

fof(ordsuccDef, axiom, ![N]: ordsucc(N) = binunion(N, sing(N))).
fof(ordsuccI1, axiom, ![N,X]: (elt(X,N) => elt(X,ordsucc(N)))).
fof(ordsuccI2, axiom, ![N]: elt(N, ordsucc(N))).
fof(ordsuccE, axiom, ![N,X]: (elt(X,ordsucc(N)) => (elt(X,N) | X = N))).

fof(adjoinEquip, axiom, ![N,X,Y]: (
    natp(N) & equip(N,X) & ~elt(Y,X)
    => equip(ordsucc(N), binunion(X,sing(Y)))
)).

fof(addNat0R, axiom, ![N]: addnat(N,n0) = N).
fof(addNatSR, axiom, ![N,M]: (natp(M) => addnat(N,ordsucc(M)) = ordsucc(addnat(N,M)))).

fof(natp0, axiom, natp(n0)).
fof(natpSucc, axiom, ![N]: (natp(N) => natp(ordsucc(N)))).

%----Base case: M + 0 = M, A union empty = A
fof(binunionEmpty, axiom, ![X]: binunion(X,n0) = X).
fof(disjointEmpty, axiom, ![A]: disjoint(A,n0)).

%----Key lemma: disjoint is preserved when adding element not in A
fof(disjointAdjoin, axiom, ![A,B,Y]: (
    disjoint(A,B) & ~elt(Y,A) 
    => disjoint(A, binunion(B,sing(Y)))
)).

%----Binunion associativity
fof(binunionAssoc, axiom, ![X,Y,Z]: binunion(X,binunion(Y,Z)) = binunion(binunion(X,Y),Z)).

%----GOAL: For all M,N,A,B
fof(goal, conjecture, ![M,N,A,B]: (
    natp(M) & natp(N) & 
    equip(M,A) & equip(N,B) & 
    disjoint(A,B)
    => equip(addnat(M,N), binunion(A,B))
)).
