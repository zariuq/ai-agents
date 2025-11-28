% TPTP formulation: 27 is odd, cannot equal 2k
% For the handshake lemma contradiction in no_3_regular_9

% Natural numbers
fof(nat_0, axiom, nat(0)).
fof(nat_succ, axiom, ![N]: (nat(N) => nat(s(N)))).

% Addition
fof(add_0, axiom, ![N]: add(0, N) = N).
fof(add_succ, axiom, ![M,N]: add(s(M), N) = s(add(M, N))).

% Multiplication
fof(mul_0, axiom, ![N]: mul(0, N) = 0).
fof(mul_succ, axiom, ![M,N]: mul(s(M), N) = add(N, mul(M, N))).

% Define 1-10
fof(def_1, axiom, n1 = s(0)).
fof(def_2, axiom, n2 = s(n1)).
fof(def_3, axiom, n3 = s(n2)).
fof(def_9, axiom, n9 = s(s(s(s(s(s(s(s(s(0)))))))))).
fof(def_27, axiom, n27 = mul(n9, n3)).

% Even/Odd
fof(even_def, axiom, ![N]: (even(N) <=> ?[K]: (nat(K) & N = mul(n2, K)))).
fof(odd_def, axiom, ![N]: (odd(N) <=> ?[K]: (nat(K) & N = add(mul(n2, K), n1)))).

% Basic fact: no number is both even and odd
fof(even_odd_exclusive, axiom, ![N]: ~(even(N) & odd(N))).

% 27 is odd
fof(twenty_seven_odd, axiom, odd(n27)).

% Conjecture: 27 cannot equal 2k for any k
fof(goal, conjecture, ![K]: (nat(K) => n27 != mul(n2, K))).
