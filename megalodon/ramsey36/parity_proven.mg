Theorem even_nat_not_odd_nat : forall x0, even_nat x0 -> not (odd_nat x0).
let x0: set.
assume H0: even_nat x0.
exact (H0 (not (odd_nat x0)) (fun H1: x0 :e omega =>(fun H2: (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) =>(H2 (not (odd_nat x0)) (fun x1: set => (fun H3: (fun x2 : set => and (x2 :e omega) (x0 = mul_nat 2 x2)) x1 =>(H3 (not (odd_nat x0)) (fun H4: x1 :e omega =>(fun H5: x0 = mul_nat 2 x1 =>(fun H6: odd_nat x0 =>(H6 False (fun H7: x0 :e omega =>(fun H8: (forall x2, x2 :e omega -> x0 = mul_nat 2 x2 -> (forall x3 : prop, x3)) =>(H8 x1 H4 H5)))))))))))))).
Qed.

Axiom odd_nat_mul_nat : forall x0 x1, odd_nat x0 -> odd_nat x1 -> odd_nat (mul_nat x0 x1).

Theorem nat_p_3 : nat_p 3.
exact nat_ordsucc 2 nat_2.
Qed.

Theorem nat_p_9 : nat_p 9.
exact nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))).
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

