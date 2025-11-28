% Theorem: no_3_regular_9
% Goal: 3-regular graph on 9 vertices has even degree sum, but 9*3=27 is odd

fof(natp3, axiom, natp(n3)).
fof(natp9, axiom, natp(n9)).
fof(natp27, axiom, natp(n27)).

fof(oddDef, axiom, ![N]: (odd(N) <=> (natp(N) & ![M]: (natp(M) => N != mul(n2,M))))).
fof(evenDef, axiom, ![N]: (even(N) <=> (natp(N) & ? [M]: (natp(M) & N = mul(n2,M))))).

fof(evenNotOdd, axiom, ![N]: (even(N) => ~odd(N))).
fof(odd27, axiom, odd(n27)).
fof(nineTimesThree, axiom, mul(n9,n3) = n27).

fof(rsym, hypothesis, symmetric(r)).
fof(reg3, hypothesis, regular3(n9,r)).

fof(regular3Def, axiom, ![V,R]: (regular3(V,R) <=>
    (![VX]: (elt(VX,V) => 
        (? [N]: (subset(N,V) & equip(n3,N) &
                 (![X]: (elt(X,N) => (rel(R,VX,X) & X != VX))) &
                 (![X]: (elt(X,V) & X != VX & rel(R,VX,X) => elt(X,N))))))))).

fof(degreeSum, axiom, ![V,R]: (symmetric(R) & regular3(V,R) & equip(n9,V) => 
    degreesumis(V,R,mul(n9,n3)))).

fof(handshake, axiom, ![V,R,S]: (degreesumis(V,R,S) => even(S))).

fof(goal, conjecture, false).
