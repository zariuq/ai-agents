% Prove that even_nat and odd_nat are mutually exclusive
% From definitions:
% even_nat n := n ∈ ω ∧ ∃m ∈ ω. n = 2*m
% odd_nat n := n ∈ ω ∧ ∀m ∈ ω. n ≠ 2*m

fof(two_in_omega, axiom, omega(two)).

fof(even_nat_def, axiom,
    ![N]: (even_nat(N) <=> (omega(N) & ?[M]: (omega(M) & N = mul(two, M))))).

fof(odd_nat_def, axiom,
    ![N]: (odd_nat(N) <=> (omega(N) & ![M]: (omega(M) => N != mul(two, M))))).

fof(goal, conjecture,
    ![N]: ~(even_nat(N) & odd_nat(N))).
