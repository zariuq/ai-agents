Theorem even_nat_not_odd_nat : forall x0, even_nat x0 -> not (odd_nat x0).
let x0: set.
assume H0: even_nat x0.
exact (H0 (not (odd_nat x0)) (fun H1: x0 :e omega =>(fun H2: (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) =>(H2 (not (odd_nat x0)) (fun x1: set => (fun H3: (fun x2 : set => and (x2 :e omega) (x0 = mul_nat 2 x2)) x1 =>(H3 (not (odd_nat x0)) (fun H4: x1 :e omega =>(fun H5: x0 = mul_nat 2 x1 =>(fun H6: odd_nat x0 =>(H6 False (fun H7: x0 :e omega =>(fun H8: (forall x2, x2 :e omega -> x0 = mul_nat 2 x2 -> (forall x3 : prop, x3)) =>(H8 x1 H4 H5)))))))))))))).
Qed.

Axiom even_nat_xor_S : forall x0, nat_p x0 -> exactly1of2 (even_nat x0) (even_nat (ordsucc x0)).
Axiom even_nat_or_odd_nat : forall x0, nat_p x0 -> or (even_nat x0) (odd_nat x0).
Axiom odd_nat_iff_odd_mul_nat : forall x0, odd_nat x0 -> forall x1, nat_p x1 -> iff (odd_nat x1) (odd_nat (mul_nat x0 x1)).

Theorem odd_nat_1 : odd_nat 1.
exact (andI (1 :e omega) (forall x0, x0 :e omega -> 1 = mul_nat 2 x0 -> (forall x1 : prop, x1)) (nat_p_omega 1 nat_1) (fun x0: set => (fun H0: x0 :e omega =>(fun H1: 1 = mul_nat 2 x0 =>(nat_inv x0 (omega_nat_p x0 H0) False (fun H2: x0 = 0 =>(neq_1_0 ((fun x1 x2: set => (fun H3: (forall x3 : set -> prop, x3 x2 -> x3 x1) =>(fun x3: set -> set -> prop => (H3 (fun x4 : set => x3 x4 x2 -> x3 x2 x4) (fun H4: x3 x2 x2 =>H4))))) 1 0 (fun x1: set -> prop => (fun H3: x1 0 =>(H1 (fun x2 : set => x1) (H2 (fun x2 x3 : set => mul_nat 2 x3 = 0) (mul_nat_0R 2) (fun x2 : set => x1) H3))))))) (fun H2: (exists x1, and (nat_p x1) (x0 = ordsucc x1)) =>(H2 False (fun x1: set => (fun H3: (fun x2 : set => and (nat_p x2) (x0 = ordsucc x2)) x1 =>(H3 False (fun H4: nat_p x1 =>(fun H5: x0 = ordsucc x1 =>(In_irref 1 (H1 (fun x2 x3 : set => 1 :e x3) (H5 (fun x2 x3 : set => 1 :e mul_nat 2 x3) (mul_nat_SR 2 x1 H4 (fun x2 x3 : set => 1 :e x3) ((fun H6: nat_p (mul_nat 2 x1) =>(add_nat_SL 1 nat_1 (mul_nat 2 x1) H6 (fun x2 x3 : set => 1 :e x3) (add_nat_SL 0 nat_0 (mul_nat 2 x1) H6 (fun x2 x3 : set => 1 :e ordsucc x3) (add_nat_0L (mul_nat 2 x1) H6 (fun x2 x3 : set => 1 :e ordsucc (ordsucc x3)) (nat_ordsucc_in_ordsucc (ordsucc (mul_nat 2 x1)) (nat_ordsucc (mul_nat 2 x1) H6) 0 (nat_0_in_ordsucc (mul_nat 2 x1) H6)))))) (mul_nat_p 2 nat_2 x1 H4)))))))))))))))))).
Qed.

Theorem odd_nat_even_nat_S : forall x0, odd_nat x0 -> even_nat (ordsucc x0).
let x0: set.
assume H0: odd_nat x0.
exact (H0 (even_nat (ordsucc x0)) (fun H1: x0 :e omega =>(fun H2: (forall x1, x1 :e omega -> x0 = mul_nat 2 x1 -> (forall x2 : prop, x2)) =>(exactly1of2_E (even_nat x0) (even_nat (ordsucc x0)) (even_nat_xor_S x0 (omega_nat_p x0 H1)) (even_nat (ordsucc x0)) (fun H3: even_nat x0 =>(FalseE (even_nat_not_odd_nat x0 H3 H0) (not (even_nat (ordsucc x0)) -> even_nat (ordsucc x0)))) (fun H3: not (even_nat x0) =>(fun H4: even_nat (ordsucc x0) =>H4)))))).
Qed.

Theorem even_nat_odd_nat_S : forall x0, even_nat x0 -> odd_nat (ordsucc x0).
let x0: set.
assume H0: even_nat x0.
exact (H0 (odd_nat (ordsucc x0)) (fun H1: x0 :e omega =>(fun H2: (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) =>(exactly1of2_E (even_nat x0) (even_nat (ordsucc x0)) (even_nat_xor_S x0 (omega_nat_p x0 H1)) (odd_nat (ordsucc x0)) (fun H3: even_nat x0 =>(fun H4: not (even_nat (ordsucc x0)) =>(even_nat_or_odd_nat (ordsucc x0) (nat_ordsucc x0 (omega_nat_p x0 H1)) (odd_nat (ordsucc x0)) (fun H5: even_nat (ordsucc x0) =>(FalseE (H4 H5) (odd_nat (ordsucc x0)))) (fun H5: odd_nat (ordsucc x0) =>H5)))) (fun H3: not (even_nat x0) =>(FalseE (H3 H0) (even_nat (ordsucc x0) -> odd_nat (ordsucc x0)))))))).
Qed.

Theorem even_nat_2 : even_nat 2.
exact odd_nat_even_nat_S 1 odd_nat_1.
Qed.

Theorem odd_nat_3 : odd_nat 3.
exact even_nat_odd_nat_S 2 even_nat_2.
Qed.

Theorem even_nat_4 : even_nat 4.
exact odd_nat_even_nat_S 3 odd_nat_3.
Qed.

Theorem odd_nat_5 : odd_nat 5.
exact even_nat_odd_nat_S 4 even_nat_4.
Qed.

Theorem even_nat_6 : even_nat 6.
exact odd_nat_even_nat_S 5 odd_nat_5.
Qed.

Theorem odd_nat_7 : odd_nat 7.
exact even_nat_odd_nat_S 6 even_nat_6.
Qed.

Theorem even_nat_8 : even_nat 8.
exact odd_nat_even_nat_S 7 odd_nat_7.
Qed.

Theorem odd_nat_9 : odd_nat 9.
exact even_nat_odd_nat_S 8 even_nat_8.
Qed.

Theorem odd_nat_mul_nat : forall x0 x1, odd_nat x0 -> odd_nat x1 -> odd_nat (mul_nat x0 x1).
let x0 x1: set.
assume H0: odd_nat x0.
assume H1: odd_nat x1.
exact (H1 (odd_nat (mul_nat x0 x1)) (fun H2: x1 :e omega =>(fun H3: (forall x2, x2 :e omega -> x1 = mul_nat 2 x2 -> (forall x3 : prop, x3)) =>(iffEL (odd_nat x1) (odd_nat (mul_nat x0 x1)) (odd_nat_iff_odd_mul_nat x0 H0 x1 (omega_nat_p x1 H2)) H1)))).
Qed.

Theorem odd_nat_27 : odd_nat (mul_nat 9 3).
exact odd_nat_mul_nat 9 3 odd_nat_9 odd_nat_3.
Qed.

Theorem not_even_nat_27 : ~even_nat (mul_nat 9 3).
assume H: even_nat (mul_nat 9 3).
exact even_nat_not_odd_nat (mul_nat 9 3) H odd_nat_27.
Qed.
