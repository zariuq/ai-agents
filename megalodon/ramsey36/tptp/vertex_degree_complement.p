% Theorem: vertex_degree_from_complement
% Goal: equip 3 N /\ equip 5 M /\ disjoint N M -> equip 8 (N union M)

fof(equip_ref, axiom, ![X]: equip(X,X)).
fof(equip_sym, axiom, ![X,Y]: (equip(X,Y) => equip(Y,X))).
fof(equip_tra, axiom, ![X,Y,Z]: (equip(X,Y) & equip(Y,Z) => equip(X,Z))).

fof(subset_ref, axiom, ![X]: subset(X,X)).
fof(subset_tra, axiom, ![X,Y,Z]: (subset(X,Y) & subset(Y,Z) => subset(X,Z))).

fof(binunionI1, axiom, ![X,Y,Z]: (elt(Z,X) => elt(Z,binunion(X,Y)))).
fof(binunionI2, axiom, ![X,Y,Z]: (elt(Z,Y) => elt(Z,binunion(X,Y)))).
fof(binunionE, axiom, ![X,Y,Z]: (elt(Z,binunion(X,Y)) => (elt(Z,X) | elt(Z,Y)))).
fof(binunionSubq1, axiom, ![X,Y]: subset(X, binunion(X,Y))).
fof(binunionSubq2, axiom, ![X,Y]: subset(Y, binunion(X,Y))).

fof(interE1, axiom, ![X,Y,Z]: (elt(Z,inter(X,Y)) => elt(Z,X))).
fof(interE2, axiom, ![X,Y,Z]: (elt(Z,inter(X,Y)) => elt(Z,Y))).
fof(interI, axiom, ![X,Y,Z]: (elt(Z,X) & elt(Z,Y) => elt(Z,inter(X,Y)))).

fof(disjointDef, axiom, ![X,Y]: (disjoint(X,Y) <=> (inter(X,Y) = empty))).
fof(emptyNoElements, axiom, ![X]: ~elt(X, empty)).

fof(natP3, axiom, natp(n3)).
fof(natP5, axiom, natp(n5)).
fof(natP8, axiom, natp(n8)).
fof(natP9, axiom, natp(n9)).

fof(natOrdinal, axiom, ![N]: (natp(N) => ordinal(N))).

fof(disjointUnionEquip, axiom, 
    ![M,N,A,B]: (
        natp(M) & natp(N) & 
        equip(M,A) & equip(N,B) & 
        disjoint(A,B)
        => equip(addnat(M,N), binunion(A,B))
    )).

fof(threePlusFive, axiom, addnat(n3, n5) = n8).

fof(vIn9, hypothesis, elt(v, n9)).
fof(nSubset9, hypothesis, subset(nset, n9)).
fof(mSubset9, hypothesis, subset(mset, n9)).
fof(partition, hypothesis, 
    ![X]: (elt(X,n9) & X != v => (elt(X,nset) | elt(X,mset)))).
fof(nNoV, hypothesis, ![X]: (elt(X,nset) => X != v)).
fof(mNoV, hypothesis, ![X]: (elt(X,mset) => X != v)).
fof(nmDisjoint, hypothesis, inter(nset,mset) = empty).
fof(nCard3, hypothesis, equip(n3, nset)).
fof(mCard5, hypothesis, equip(n5, mset)).

fof(goal, conjecture, equip(n8, binunion(nset,mset))).
