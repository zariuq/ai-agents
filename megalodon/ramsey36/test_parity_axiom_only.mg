Axiom even_nat_not_odd_nat : forall x0, even_nat x0 -> not (odd_nat x0).
Axiom odd_nat_mul_nat : forall x0 x1, odd_nat x0 -> odd_nat x1 -> odd_nat (mul_nat x0 x1).

Theorem nat_p_9 : nat_p 9.
exact nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))).
Qed.

Theorem nat_p_3 : nat_p 3.
exact nat_ordsucc 2 nat_2.
Qed.

Axiom odd_nat_3 : odd_nat 3.
Axiom odd_nat_9 : odd_nat 9.

Theorem odd_nat_27 : odd_nat (mul_nat 9 3).
exact odd_nat_mul_nat 9 3 odd_nat_9 odd_nat_3.
Qed.

Theorem not_even_nat_27 : ~even_nat (mul_nat 9 3).
assume H: even_nat (mul_nat 9 3).
exact even_nat_not_odd_nat (mul_nat 9 3) H odd_nat_27.
Qed.
