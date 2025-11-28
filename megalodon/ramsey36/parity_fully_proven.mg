Theorem even_nat_0 : even_nat 0.
exact (andI (0 :e omega) (exists x0, and (x0 :e omega) (0 = mul_nat 2 x0)) (nat_p_omega 0 nat_0) (fun x0: prop => (fun H0: (forall x1, and (x1 :e omega) (0 = mul_nat 2 x1) -> x0) =>(H0 0 (andI (0 :e omega) (0 = mul_nat 2 0) (nat_p_omega 0 nat_0) (fun x1: set -> set -> prop => (mul_nat_0R 2 (fun x2 x3 : set => x1 x3 x2)))))))).
Qed.

Theorem even_nat_not_odd_nat : forall x0, even_nat x0 -> not (odd_nat x0).
let x0: set.
assume H0: even_nat x0.
exact (H0 (not (odd_nat x0)) (fun H1: x0 :e omega =>(fun H2: (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) =>(H2 (not (odd_nat x0)) (fun x1: set => (fun H3: (fun x2 : set => and (x2 :e omega) (x0 = mul_nat 2 x2)) x1 =>(H3 (not (odd_nat x0)) (fun H4: x1 :e omega =>(fun H5: x0 = mul_nat 2 x1 =>(fun H6: odd_nat x0 =>(H6 False (fun H7: x0 :e omega =>(fun H8: (forall x2, x2 :e omega -> x0 = mul_nat 2 x2 -> (forall x3 : prop, x3)) =>(H8 x1 H4 H5)))))))))))))).
Qed.

Theorem odd_nat_1 : odd_nat 1.
exact (andI (1 :e omega) (forall x0, x0 :e omega -> 1 = mul_nat 2 x0 -> (forall x1 : prop, x1)) (nat_p_omega 1 nat_1) (fun x0: set => (fun H0: x0 :e omega =>(fun H1: 1 = mul_nat 2 x0 =>(nat_inv x0 (omega_nat_p x0 H0) False (fun H2: x0 = 0 =>(neq_1_0 ((fun x1 x2: set => (fun H3: (forall x3 : set -> prop, x3 x2 -> x3 x1) =>(fun x3: set -> set -> prop => (H3 (fun x4 : set => x3 x4 x2 -> x3 x2 x4) (fun H4: x3 x2 x2 =>H4))))) 1 0 (fun x1: set -> prop => (fun H3: x1 0 =>(H1 (fun x2 : set => x1) (H2 (fun x2 x3 : set => mul_nat 2 x3 = 0) (mul_nat_0R 2) (fun x2 : set => x1) H3))))))) (fun H2: (exists x1, and (nat_p x1) (x0 = ordsucc x1)) =>(H2 False (fun x1: set => (fun H3: (fun x2 : set => and (nat_p x2) (x0 = ordsucc x2)) x1 =>(H3 False (fun H4: nat_p x1 =>(fun H5: x0 = ordsucc x1 =>(In_irref 1 (H1 (fun x2 x3 : set => 1 :e x3) (H5 (fun x2 x3 : set => 1 :e mul_nat 2 x3) (mul_nat_SR 2 x1 H4 (fun x2 x3 : set => 1 :e x3) ((fun H6: nat_p (mul_nat 2 x1) =>(add_nat_SL 1 nat_1 (mul_nat 2 x1) H6 (fun x2 x3 : set => 1 :e x3) (add_nat_SL 0 nat_0 (mul_nat 2 x1) H6 (fun x2 x3 : set => 1 :e ordsucc x3) (add_nat_0L (mul_nat 2 x1) H6 (fun x2 x3 : set => 1 :e ordsucc (ordsucc x3)) (nat_ordsucc_in_ordsucc (ordsucc (mul_nat 2 x1)) (nat_ordsucc (mul_nat 2 x1) H6) 0 (nat_0_in_ordsucc (mul_nat 2 x1) H6)))))) (mul_nat_p 2 nat_2 x1 H4)))))))))))))))))).
Qed.
Theorem even_nat_double : (forall x0, nat_p x0 -> even_nat (mul_nat 2 x0)).
let x0: set.
assume H0: nat_p x0.
exact (andI (mul_nat 2 x0 :e omega) (exists x1, and (x1 :e omega) (mul_nat 2 x0 = mul_nat 2 x1)) (nat_p_omega (mul_nat 2 x0) (mul_nat_p 2 nat_2 x0 H0)) (fun x1: prop => (fun H1: (forall x2, and (x2 :e omega) (mul_nat 2 x0 = mul_nat 2 x2) -> x1) =>(H1 x0 (andI (x0 :e omega) (mul_nat 2 x0 = mul_nat 2 x0) (nat_p_omega x0 H0) (fun x2: set -> set -> prop => (fun H2: x2 (mul_nat 2 x0) (mul_nat 2 x0) =>H2))))))).
Qed.

Theorem even_nat_S_S : (forall x0, even_nat x0 -> even_nat (ordsucc (ordsucc x0))).
let x0: set.
assume H0: even_nat x0.
exact (H0 (even_nat (ordsucc (ordsucc x0))) (fun H1: x0 :e omega =>(fun H2: (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) =>(H2 (even_nat (ordsucc (ordsucc x0))) (fun x1: set => (fun H3: (fun x2 : set => and (x2 :e omega) (x0 = mul_nat 2 x2)) x1 =>(H3 (even_nat (ordsucc (ordsucc x0))) (fun H4: x1 :e omega =>(fun H5: x0 = mul_nat 2 x1 =>(andI (ordsucc (ordsucc x0) :e omega) (exists x2, and (x2 :e omega) (ordsucc (ordsucc x0) = mul_nat 2 x2)) (omega_ordsucc (ordsucc x0) (omega_ordsucc x0 H1)) (fun x2: prop => (fun H6: (forall x3, and (x3 :e omega) (ordsucc (ordsucc x0) = mul_nat 2 x3) -> x2) =>(H6 (ordsucc x1) (andI (ordsucc x1 :e omega) (ordsucc (ordsucc x0) = mul_nat 2 (ordsucc x1)) (omega_ordsucc x1 H4) (mul_nat_SR 2 x1 (omega_nat_p x1 H4) (fun x3 x4 : set => ordsucc (ordsucc x0) = x4) (H5 (fun x3 x4 : set => ordsucc (ordsucc x0) = add_nat 2 x3) (add_nat_SL 1 nat_1 x0 (omega_nat_p x0 H1) (fun x3 x4 : set => ordsucc (ordsucc x0) = x4) ((fun x3 x4: set => (fun H7: (forall x5 : set -> prop, x5 x4 -> x5 x3) =>(fun x5: set -> set -> prop => (H7 (fun x6 : set => x5 x6 x4 -> x5 x4 x6) (fun H8: x5 x4 x4 =>H8))))) (ordsucc (ordsucc x0)) (ordsucc (add_nat 1 x0)) (fun x3: set -> prop => (fun H7: x3 (ordsucc (add_nat 1 x0)) =>((fun x4: set -> set -> prop => (add_nat_SL 0 nat_0 x0 (omega_nat_p x0 H1) (fun x5 x6 : set => ordsucc x0 = x6) ((fun x5 x6: set => (fun H8: (forall x7 : set -> prop, x7 x6 -> x7 x5) =>(fun x7: set -> set -> prop => (H8 (fun x8 : set => x7 x8 x6 -> x7 x6 x8) (fun H9: x7 x6 x6 =>H9))))) (ordsucc x0) (ordsucc (add_nat 0 x0)) (fun x5: set -> prop => (fun H8: x5 (ordsucc (add_nat 0 x0)) =>((fun x6: set -> set -> prop => ((fun x7: set -> set -> prop => (add_nat_0L x0 (omega_nat_p x0 H1) (fun x8 x9 : set => x7 x9 x8))) (fun x7 x8 : set => x6 (ordsucc x7) (ordsucc x8)))) (fun x6 : set => x5) H8)))) (fun x5 x6 : set => x4 (ordsucc x5) (ordsucc x6)))) (fun x4 : set => x3) H7))))))))))))))))))))).
Qed.

Theorem even_nat_S_S_inv : (forall x0, nat_p x0 -> even_nat (ordsucc (ordsucc x0)) -> even_nat x0).
let x0: set.
assume H0: nat_p x0.
assume H1: even_nat (ordsucc (ordsucc x0)).
exact (H1 (even_nat x0) (fun H2: ordsucc (ordsucc x0) :e omega =>(fun H3: (exists x1, and (x1 :e omega) (ordsucc (ordsucc x0) = mul_nat 2 x1)) =>(andI (x0 :e omega) (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) (nat_p_omega x0 H0) (H3 (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) (fun x1: set => (fun H4: (fun x2 : set => and (x2 :e omega) (ordsucc (ordsucc x0) = mul_nat 2 x2)) x1 =>(H4 (exists x2, and (x2 :e omega) (x0 = mul_nat 2 x2)) (fun H5: x1 :e omega =>(fun H6: ordsucc (ordsucc x0) = mul_nat 2 x1 =>(nat_inv x1 (omega_nat_p x1 H5) (exists x2, and (x2 :e omega) (x0 = mul_nat 2 x2)) (fun H7: x1 = 0 =>(neq_ordsucc_0 (ordsucc x0) ((fun x2 x3: set => (fun H8: (forall x4 : set -> prop, x4 x3 -> x4 x2) =>(fun x4: set -> set -> prop => (H8 (fun x5 : set => x4 x5 x3 -> x4 x3 x5) (fun H9: x4 x3 x3 =>H9))))) (ordsucc (ordsucc x0)) 0 (fun x2: set -> prop => (fun H8: x2 0 =>(H6 (fun x3 : set => x2) (H7 (fun x3 x4 : set => mul_nat 2 x4 = 0) (mul_nat_0R 2) (fun x3 : set => x2) H8))))) (exists x2, and (x2 :e omega) (x0 = mul_nat 2 x2)))) (fun H7: (exists x2, and (nat_p x2) (x1 = ordsucc x2)) =>(H7 (exists x2, and (x2 :e omega) (x0 = mul_nat 2 x2)) (fun x2: set => (fun H8: (fun x3 : set => and (nat_p x3) (x1 = ordsucc x3)) x2 =>(H8 (exists x3, and (x3 :e omega) (x0 = mul_nat 2 x3)) (fun H9: nat_p x2 =>(fun H10: x1 = ordsucc x2 =>(fun x3: prop => (fun H11: (forall x4, and (x4 :e omega) (x0 = mul_nat 2 x4) -> x3) =>(H11 x2 (andI (x2 :e omega) (x0 = mul_nat 2 x2) (nat_p_omega x2 H9) (ordsucc_inj x0 (mul_nat 2 x2) (ordsucc_inj (ordsucc x0) (ordsucc (mul_nat 2 x2)) (H6 (fun x4 x5 : set => x5 = ordsucc (ordsucc (mul_nat 2 x2))) (H10 (fun x4 x5 : set => mul_nat 2 x5 = ordsucc (ordsucc (mul_nat 2 x2))) (mul_nat_SR 2 x2 H9 (fun x4 x5 : set => x5 = ordsucc (ordsucc (mul_nat 2 x2))) ((fun H12: nat_p (mul_nat 2 x2) =>(add_nat_SL 1 nat_1 (mul_nat 2 x2) H12 (fun x4 x5 : set => x5 = ordsucc (ordsucc (mul_nat 2 x2))) ((fun x4 x5: set => (fun H13: (forall x6 : set -> prop, x6 x5 -> x6 x4) =>(fun x6: set -> set -> prop => (H13 (fun x7 : set => x6 x7 x5 -> x6 x5 x7) (fun H14: x6 x5 x5 =>H14))))) (ordsucc (add_nat 1 (mul_nat 2 x2))) (ordsucc (ordsucc (mul_nat 2 x2))) (fun x4: set -> prop => (fun H13: x4 (ordsucc (ordsucc (mul_nat 2 x2))) =>((fun x5: set -> set -> prop => (add_nat_SL 0 nat_0 (mul_nat 2 x2) H12 (fun x6 x7 : set => x7 = ordsucc (mul_nat 2 x2)) ((fun x6 x7: set => (fun H14: (forall x8 : set -> prop, x8 x7 -> x8 x6) =>(fun x8: set -> set -> prop => (H14 (fun x9 : set => x8 x9 x7 -> x8 x7 x9) (fun H15: x8 x7 x7 =>H15))))) (ordsucc (add_nat 0 (mul_nat 2 x2))) (ordsucc (mul_nat 2 x2)) (fun x6: set -> prop => (fun H14: x6 (ordsucc (mul_nat 2 x2)) =>((fun x7: set -> set -> prop => (add_nat_0L (mul_nat 2 x2) H12 (fun x8 x9 : set => x7 (ordsucc x8) (ordsucc x9)))) (fun x7 : set => x6) H14)))) (fun x6 x7 : set => x5 (ordsucc x6) (ordsucc x7)))) (fun x5 : set => x4) H13)))))) (mul_nat_p 2 nat_2 x2 H9))))))))))))))))))))))))))))).
Qed.

Theorem even_nat_xor_S : (forall x0, nat_p x0 -> exactly1of2 (even_nat x0) (even_nat (ordsucc x0))).
exact (nat_ind (fun x0 : set => exactly1of2 (even_nat x0) (even_nat (ordsucc x0))) (exactly1of2_I1 (even_nat 0) (even_nat 1) (andI (0 :e omega) (exists x0, and (x0 :e omega) (0 = mul_nat 2 x0)) (nat_p_omega 0 nat_0) (fun x0: prop => (fun H0: (forall x1, and (x1 :e omega) (0 = mul_nat 2 x1) -> x0) =>(H0 0 (andI (0 :e omega) (0 = mul_nat 2 0) (nat_p_omega 0 nat_0) (fun x1: set -> set -> prop => (mul_nat_0R 2 (fun x2 x3 : set => x1 x3 x2)))))))) (fun H0: even_nat 1 =>(even_nat_not_odd_nat 1 H0 odd_nat_1))) (fun x0: set => (fun H0: nat_p x0 =>(fun H1: exactly1of2 (even_nat x0) (even_nat (ordsucc x0)) =>(exactly1of2_E (even_nat x0) (even_nat (ordsucc x0)) H1 (exactly1of2 (even_nat (ordsucc x0)) (even_nat (ordsucc (ordsucc x0)))) (fun H2: even_nat x0 =>(fun H3: not (even_nat (ordsucc x0)) =>(exactly1of2_I2 (even_nat (ordsucc x0)) (even_nat (ordsucc (ordsucc x0))) H3 (even_nat_S_S x0 H2)))) (fun H2: not (even_nat x0) =>(fun H3: even_nat (ordsucc x0) =>(exactly1of2_I1 (even_nat (ordsucc x0)) (even_nat (ordsucc (ordsucc x0))) H3 (fun H4: even_nat (ordsucc (ordsucc x0)) =>(H2 (even_nat_S_S_inv x0 H0 H4))))))))))).
Qed.

Theorem even_nat_or_odd_nat : (forall x0, nat_p x0 -> or (even_nat x0) (odd_nat x0)).
exact (nat_ind (fun x0 : set => or (even_nat x0) (odd_nat x0)) (orIL (even_nat 0) (odd_nat 0) even_nat_0) (fun x0: set => (fun H0: nat_p x0 =>(fun H1: or (even_nat x0) (odd_nat x0) =>(H1 (or (even_nat (ordsucc x0)) (odd_nat (ordsucc x0))) (fun H2: even_nat x0 =>(orIR (even_nat (ordsucc x0)) (odd_nat (ordsucc x0)) (exactly1of2_E (even_nat x0) (even_nat (ordsucc x0)) (even_nat_xor_S x0 H0) (odd_nat (ordsucc x0)) (fun H3: even_nat x0 =>(fun H4: not (even_nat (ordsucc x0)) =>(andI (ordsucc x0 :e omega) (forall x1, x1 :e omega -> ordsucc x0 = mul_nat 2 x1 -> (forall x2 : prop, x2)) (omega_ordsucc x0 (nat_p_omega x0 H0)) (fun x1: set => (fun H5: x1 :e omega =>(fun H6: ordsucc x0 = mul_nat 2 x1 =>(H4 (andI (ordsucc x0 :e omega) (exists x2, and (x2 :e omega) (ordsucc x0 = mul_nat 2 x2)) (omega_ordsucc x0 (nat_p_omega x0 H0)) (fun x2: prop => (fun H7: (forall x3, and (x3 :e omega) (ordsucc x0 = mul_nat 2 x3) -> x2) =>(H7 x1 (andI (x1 :e omega) (ordsucc x0 = mul_nat 2 x1) H5 H6)))))))))))) (fun H3: not (even_nat x0) =>(FalseE (H3 H2) (even_nat (ordsucc x0) -> odd_nat (ordsucc x0))))))) (fun H2: odd_nat x0 =>(orIL (even_nat (ordsucc x0)) (odd_nat (ordsucc x0)) (exactly1of2_E (even_nat x0) (even_nat (ordsucc x0)) (even_nat_xor_S x0 H0) (even_nat (ordsucc x0)) (fun H3: even_nat x0 =>(FalseE (even_nat_not_odd_nat x0 H3 H2) (not (even_nat (ordsucc x0)) -> even_nat (ordsucc x0)))) (fun H3: not (even_nat x0) =>(fun H4: even_nat (ordsucc x0) =>H4)))))))))).
Qed.

Theorem not_odd_nat_0 : not (odd_nat 0).
assume H0: odd_nat 0.
exact (even_nat_not_odd_nat 0 even_nat_0 H0).
Qed.

Theorem even_nat_odd_nat_S : (forall x0, even_nat x0 -> odd_nat (ordsucc x0)).
let x0: set.
assume H0: even_nat x0.
exact (H0 (odd_nat (ordsucc x0)) (fun H1: x0 :e omega =>(fun H2: (exists x1, and (x1 :e omega) (x0 = mul_nat 2 x1)) =>(exactly1of2_E (even_nat x0) (even_nat (ordsucc x0)) (even_nat_xor_S x0 (omega_nat_p x0 H1)) (odd_nat (ordsucc x0)) (fun H3: even_nat x0 =>(fun H4: not (even_nat (ordsucc x0)) =>(even_nat_or_odd_nat (ordsucc x0) (nat_ordsucc x0 (omega_nat_p x0 H1)) (odd_nat (ordsucc x0)) (fun H5: even_nat (ordsucc x0) =>(FalseE (H4 H5) (odd_nat (ordsucc x0)))) (fun H5: odd_nat (ordsucc x0) =>H5)))) (fun H3: not (even_nat x0) =>(FalseE (H3 H0) (even_nat (ordsucc x0) -> odd_nat (ordsucc x0)))))))).
Qed.

Theorem odd_nat_even_nat_S : (forall x0, odd_nat x0 -> even_nat (ordsucc x0)).
let x0: set.
assume H0: odd_nat x0.
exact (H0 (even_nat (ordsucc x0)) (fun H1: x0 :e omega =>(fun H2: (forall x1, x1 :e omega -> x0 = mul_nat 2 x1 -> (forall x2 : prop, x2)) =>(exactly1of2_E (even_nat x0) (even_nat (ordsucc x0)) (even_nat_xor_S x0 (omega_nat_p x0 H1)) (even_nat (ordsucc x0)) (fun H3: even_nat x0 =>(FalseE (even_nat_not_odd_nat x0 H3 H0) (not (even_nat (ordsucc x0)) -> even_nat (ordsucc x0)))) (fun H3: not (even_nat x0) =>(fun H4: even_nat (ordsucc x0) =>H4)))))).
Qed.

Theorem odd_nat_xor_odd_sum : (forall x0, odd_nat x0 -> (forall x1, nat_p x1 -> exactly1of2 (odd_nat x1) (odd_nat (add_nat x0 x1)))).
let x0: set.
assume H0: odd_nat x0.
exact (H0 (forall x1, nat_p x1 -> exactly1of2 (odd_nat x1) (odd_nat (add_nat x0 x1))) (fun H1: x0 :e omega =>(fun H2: (forall x1, x1 :e omega -> x0 = mul_nat 2 x1 -> (forall x2 : prop, x2)) =>(nat_ind (fun x1 : set => exactly1of2 (odd_nat x1) (odd_nat (add_nat x0 x1))) (add_nat_0R x0 (fun x1 x2 : set => exactly1of2 (odd_nat 0) (odd_nat x2)) (exactly1of2_I2 (odd_nat 0) (odd_nat x0) not_odd_nat_0 H0)) (fun x1: set => (fun H3: nat_p x1 =>(fun H4: exactly1of2 (odd_nat x1) (odd_nat (add_nat x0 x1)) =>(add_nat_SR x0 x1 H3 (fun x2 x3 : set => exactly1of2 (odd_nat (ordsucc x1)) (odd_nat x3)) (exactly1of2_E (odd_nat x1) (odd_nat (add_nat x0 x1)) H4 (exactly1of2 (odd_nat (ordsucc x1)) (odd_nat (ordsucc (add_nat x0 x1)))) (fun H5: odd_nat x1 =>(fun H6: not (odd_nat (add_nat x0 x1)) =>(exactly1of2_I2 (odd_nat (ordsucc x1)) (odd_nat (ordsucc (add_nat x0 x1))) (even_nat_not_odd_nat (ordsucc x1) (odd_nat_even_nat_S x1 H5)) (even_nat_odd_nat_S (add_nat x0 x1) (even_nat_or_odd_nat (add_nat x0 x1) (add_nat_p x0 (omega_nat_p x0 H1) x1 H3) (even_nat (add_nat x0 x1)) (fun H7: even_nat (add_nat x0 x1) =>H7) (fun H7: odd_nat (add_nat x0 x1) =>(FalseE (H6 H7) (even_nat (add_nat x0 x1))))))))) (fun H5: not (odd_nat x1) =>(fun H6: odd_nat (add_nat x0 x1) =>(exactly1of2_I1 (odd_nat (ordsucc x1)) (odd_nat (ordsucc (add_nat x0 x1))) (even_nat_odd_nat_S x1 (even_nat_or_odd_nat x1 H3 (even_nat x1) (fun H7: even_nat x1 =>H7) (fun H7: odd_nat x1 =>(FalseE (H5 H7) (even_nat x1))))) (even_nat_not_odd_nat (ordsucc (add_nat x0 x1)) (odd_nat_even_nat_S (add_nat x0 x1) H6)))))))))))))).
Qed.

Theorem odd_nat_iff_odd_mul_nat : (forall x0, odd_nat x0 -> (forall x1, nat_p x1 -> iff (odd_nat x1) (odd_nat (mul_nat x0 x1)))).
let x0: set.
assume H0: odd_nat x0.
exact (H0 (forall x1, nat_p x1 -> iff (odd_nat x1) (odd_nat (mul_nat x0 x1))) (fun H1: x0 :e omega =>(fun H2: (forall x1, x1 :e omega -> x0 = mul_nat 2 x1 -> (forall x2 : prop, x2)) =>(nat_ind (fun x1 : set => iff (odd_nat x1) (odd_nat (mul_nat x0 x1))) (mul_nat_0R x0 (fun x1 x2 : set => iff (odd_nat 0) (odd_nat x2)) (iff_refl (odd_nat 0))) (fun x1: set => (fun H3: nat_p x1 =>(fun H4: iff (odd_nat x1) (odd_nat (mul_nat x0 x1)) =>(mul_nat_SR x0 x1 H3 (fun x2 x3 : set => iff (odd_nat (ordsucc x1)) (odd_nat x3)) (iffI (odd_nat (ordsucc x1)) (odd_nat (add_nat x0 (mul_nat x0 x1))) (fun H5: odd_nat (ordsucc x1) =>(exactly1of2_E (odd_nat (mul_nat x0 x1)) (odd_nat (add_nat x0 (mul_nat x0 x1))) (odd_nat_xor_odd_sum x0 H0 (mul_nat x0 x1) (mul_nat_p x0 (omega_nat_p x0 H1) x1 H3)) (odd_nat (add_nat x0 (mul_nat x0 x1))) (fun H6: odd_nat (mul_nat x0 x1) =>(fun H7: not (odd_nat (add_nat x0 (mul_nat x0 x1))) =>((fun H8: odd_nat x1 =>(FalseE (even_nat_not_odd_nat (ordsucc x1) (odd_nat_even_nat_S x1 H8) H5) (odd_nat (add_nat x0 (mul_nat x0 x1))))) (iffER (odd_nat x1) (odd_nat (mul_nat x0 x1)) H4 H6)))) (fun H6: not (odd_nat (mul_nat x0 x1)) =>(fun H7: odd_nat (add_nat x0 (mul_nat x0 x1)) =>H7)))) (fun H5: odd_nat (add_nat x0 (mul_nat x0 x1)) =>(even_nat_odd_nat_S x1 (exactly1of2_E (odd_nat (mul_nat x0 x1)) (odd_nat (add_nat x0 (mul_nat x0 x1))) (odd_nat_xor_odd_sum x0 H0 (mul_nat x0 x1) (mul_nat_p x0 (omega_nat_p x0 H1) x1 H3)) (even_nat x1) (fun H6: odd_nat (mul_nat x0 x1) =>(fun H7: not (odd_nat (add_nat x0 (mul_nat x0 x1))) =>(FalseE (H7 H5) (even_nat x1)))) (fun H6: not (odd_nat (mul_nat x0 x1)) =>(fun H7: odd_nat (add_nat x0 (mul_nat x0 x1)) =>(even_nat_or_odd_nat x1 H3 (even_nat x1) (fun H8: even_nat x1 =>H8) (fun H8: odd_nat x1 =>(FalseE (H6 (iffEL (odd_nat x1) (odd_nat (mul_nat x0 x1)) H4 H8)) (even_nat x1)))))))))))))))))).
Qed.

Theorem odd_nat_mul_nat : (forall x0 x1, odd_nat x0 -> odd_nat x1 -> odd_nat (mul_nat x0 x1)).
let x0 x1: set.
assume H0: odd_nat x0.
assume H1: odd_nat x1.
exact (H1 (odd_nat (mul_nat x0 x1)) (fun H2: x1 :e omega =>(fun H3: (forall x2, x2 :e omega -> x1 = mul_nat 2 x2 -> (forall x3 : prop, x3)) =>(iffEL (odd_nat x1) (odd_nat (mul_nat x0 x1)) (odd_nat_iff_odd_mul_nat x0 H0 x1 (omega_nat_p x1 H2)) H1)))).
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

Theorem odd_nat_27 : odd_nat (mul_nat 9 3).
exact odd_nat_mul_nat 9 3 odd_nat_9 odd_nat_3.
Qed.

Theorem not_even_nat_27 : ~even_nat (mul_nat 9 3).
assume H: even_nat (mul_nat 9 3).
exact even_nat_not_odd_nat (mul_nat 9 3) H odd_nat_27.
Qed.
