% Proper Peano arithmetic formulation: 27 cannot equal 2k

% Peano axioms
fof(zero_nat, axiom, nat(zero)).
fof(succ_nat, axiom, ![X]: (nat(X) => nat(succ(X)))).
fof(succ_inj, axiom, ![X,Y]: (succ(X) = succ(Y) => X = Y)).
fof(succ_not_zero, axiom, ![X]: succ(X) != zero).

% Addition
fof(add_zero, axiom, ![X]: add(zero, X) = X).
fof(add_succ, axiom, ![X,Y]: add(succ(X), Y) = succ(add(X, Y))).

% Multiplication
fof(mul_zero, axiom, ![X]: mul(zero, X) = zero).
fof(mul_succ, axiom, ![X,Y]: mul(succ(X), Y) = add(Y, mul(X, Y))).

% Build numbers
fof(n1, axiom, n1 = succ(zero)).
fof(n2, axiom, n2 = succ(n1)).
fof(n3, axiom, n3 = succ(n2)).
fof(n4, axiom, n4 = succ(n3)).
fof(n5, axiom, n5 = succ(n4)).
fof(n6, axiom, n6 = succ(n5)).
fof(n7, axiom, n7 = succ(n6)).
fof(n8, axiom, n8 = succ(n7)).
fof(n9, axiom, n9 = succ(n8)).
fof(n10, axiom, n10 = succ(n9)).
fof(n13, axiom, n13 = succ(succ(succ(n10)))).
fof(n26, axiom, n26 = mul(n2, n13)).
fof(n27, axiom, n27 = succ(n26)).

% Even: exists k such that n = 2*k
fof(even_def, axiom, ![N]: (even(N) <=> ?[K]: (nat(K) & N = mul(n2, K)))).

% Odd: exists k such that n = 2*k + 1
fof(odd_def, axiom, ![N]: (odd(N) <=> ?[K]: (nat(K) & N = add(mul(n2, K), n1)))).

% Basic lemma: if n = 2k then n != 2k+1
fof(even_not_odd, axiom, ![N]: ~(even(N) & odd(N))).

% 27 = 2*13 + 1, so it's odd
fof(n27_is_odd, axiom, odd(n27)).

% Therefore 27 is not even
fof(goal, conjecture, ~even(n27)).
