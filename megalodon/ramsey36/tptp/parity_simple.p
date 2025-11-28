% Simpler: just prove 27 is not even

fof(even_iff_2k, axiom, ![X]: (even(X) <=> ?[K]: X = times(s2, K))).

% Constants
fof(c27, axiom, c27 = s27).

% 27 is odd (witness: 27 = 2*13 + 1)
fof(c27_eq, axiom, c27 = plus(times(s2, s13), s1)).

% If 27 = 2k, then derive contradiction
fof(not_even, conjecture, ~even(c27)).
