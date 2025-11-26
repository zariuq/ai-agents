% General theorem: disjoint union cardinality
% If equip(m,A), equip(n,B), disjoint(A,B), then equip(m+n, A union B)

%----Bijection definition
fof(bijDef, axiom, ![X,Y,F]: (bij(X,Y,F) <=> 
    (![Z]: (elt(Z,X) => elt(app(F,Z),Y))) &
    (![Z1,Z2]: (elt(Z1,X) & elt(Z2,X) & app(F,Z1) = app(F,Z2) => Z1 = Z2)) &
    (![Z]: (elt(Z,Y) => ?[W]: (elt(W,X) & app(F,W) = Z)))
)).

%----Equip definition  
fof(equipDef, axiom, ![X,Y]: (equip(X,Y) <=> ?[F]: bij(X,Y,F))).

%----Equip properties (proven in Part1.mg)
fof(equipRef, axiom, ![X]: equip(X,X)).
fof(equipSym, axiom, ![X,Y]: (equip(X,Y) => equip(Y,X))).
fof(equipTra, axiom, ![X,Y,Z]: (equip(X,Y) & equip(Y,Z) => equip(X,Z))).

%----Binary union axioms
fof(binunionI1, axiom, ![X,Y,Z]: (elt(Z,X) => elt(Z,binunion(X,Y)))).
fof(binunionI2, axiom, ![X,Y,Z]: (elt(Z,Y) => elt(Z,binunion(X,Y)))).
fof(binunionE, axiom, ![X,Y,Z]: (elt(Z,binunion(X,Y)) => (elt(Z,X) | elt(Z,Y)))).

%----Singleton
fof(singI, axiom, ![X]: elt(X, sing(X))).
fof(singE, axiom, ![X,Y]: (elt(Y, sing(X)) => Y = X)).

%----Disjoint definition
fof(disjointDef, axiom, ![A,B]: (disjoint(A,B) <=> ![X]: ~(elt(X,A) & elt(X,B)))).

%----Ordinal successor (natural number successor)
fof(ordsuccDef, axiom, ![N]: ordsucc(N) = binunion(N, sing(N))).
fof(ordsuccI1, axiom, ![N,X]: (elt(X,N) => elt(X,ordsucc(N)))).
fof(ordsuccI2, axiom, ![N]: elt(N, ordsucc(N))).
fof(ordsuccE, axiom, ![N,X]: (elt(X,ordsucc(N)) => (elt(X,N) | X = N))).

%----Key lemma from Part1.mg: adjoin preserves equip
fof(adjoinEquip, axiom, ![N,X,Y]: (
    natp(N) & equip(N,X) & ~elt(Y,X)
    => equip(ordsucc(N), binunion(X,sing(Y)))
)).

%----Addition on naturals
fof(addNat0R, axiom, ![N]: (natp(N) => addnat(N,n0) = N)).
fof(addNatSR, axiom, ![N,M]: (natp(N) & natp(M) => addnat(N,ordsucc(M)) = ordsucc(addnat(N,M)))).
fof(addNatNatp, axiom, ![N,M]: (natp(N) & natp(M) => natp(addnat(N,M)))).

%----Natural number axioms
fof(natpOrdinal, axiom, ![N]: (natp(N) => ordinal(N))).
fof(natp0, axiom, natp(n0)).
fof(natpSucc, axiom, ![N]: (natp(N) => natp(ordsucc(N)))).

%----Induction schema for proving equip properties
fof(natInduction, axiom, ![P]: (
    P(n0) & (![N]: (natp(N) & P(N) => P(ordsucc(N))))
    => ![N]: (natp(N) => P(N))
)).

%----GOAL: General disjoint union theorem
fof(goal, conjecture, ![M,N,A,B]: (
    natp(M) & natp(N) & 
    equip(M,A) & equip(N,B) & 
    disjoint(A,B)
    => equip(addnat(M,N), binunion(A,B))
)).
