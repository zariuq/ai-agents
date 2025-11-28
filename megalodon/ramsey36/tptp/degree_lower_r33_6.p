% Theorem: degree_lower_from_r33_6
% Goal: Use R(3,3)=6 to bound degree from below

fof(triangleFree, axiom, ![V,R,X,Y,Z]: 
    (trianglefree(V,R) => (elt(X,V) & elt(Y,V) & elt(Z,V) & rel(R,X,Y) & rel(R,Y,Z) & rel(R,X,Z) => false))).

fof(twor336, axiom, tworamsey(n3,n3,n6)).

fof(tworamseyDef, axiom, ![M,N,V]: (tworamsey(M,N,V) <=>
    (![R]: (symmetric(R) => 
        ((? [X]: (subset(X,V) & equip(M,X) & ![X1,X2]: (elt(X1,X) & elt(X2,X) & X1 != X2 => rel(R,X1,X2)))) |
         (? [Y]: (subset(Y,V) & equip(N,Y) & ![Y1,Y2]: (elt(Y1,Y) & elt(Y2,Y) & Y1 != Y2 => ~rel(R,Y1,Y2))))))))).

fof(rsym, hypothesis, symmetric(r)).
fof(tfree, hypothesis, trianglefree(n9,r)).
fof(vIn9, hypothesis, elt(v,n9)).
fof(nSubset9, hypothesis, subset(nset,n9)).
fof(mSubset9, hypothesis, subset(mset,n9)).
fof(nAdj, hypothesis, ![X]: (elt(X,nset) => (rel(r,v,X) & X != v))).
fof(mNonadj, hypothesis, ![X]: (elt(X,mset) => (~rel(r,v,X) & X != v))).
fof(nCard3, hypothesis, equip(n3,nset)).
fof(mCard6, hypothesis, equip(n6,mset)).

fof(goal, conjecture, false).
