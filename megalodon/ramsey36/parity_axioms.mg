Definition even : set -> prop := fun n => exists k:set, nat_p k /\ n = mul_nat 2 k.
Definition odd : set -> prop := fun n => exists k:set, nat_p k /\ n = add_nat (mul_nat 2 k) 1.

Theorem eq_sym : forall x y:set, x = y -> y = x.
let x. let y.
assume Hxy: x = y.
prove y = x.
prove forall Q: set -> set -> prop, Q y x -> Q x y.
let Q: set -> set -> prop.
assume Hqyx: Q y x.
exact Hxy (fun a b => Q b a) Hqyx.
Qed.

Axiom even_not_odd : forall n:set, ~(even n /\ odd n).

Theorem nat_p_10 : nat_p 10.
exact nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 (nat_ordsucc 11 (nat_ordsucc 10 nat_p_10)).
Qed.

Theorem nat_p_26 : nat_p 26.
exact nat_ordsucc 25 (nat_ordsucc 24 (nat_ordsucc 23 (nat_ordsucc 22
  (nat_ordsucc 21 (nat_ordsucc 20 (nat_ordsucc 19 (nat_ordsucc 18
  (nat_ordsucc 17 (nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14
  (nat_ordsucc 13 nat_p_13)))))))))))).
Qed.

Theorem nat_p_27 : nat_p 27.
exact nat_ordsucc 26 nat_p_26.
Qed.

Axiom mul_2_13_eq_26 : mul_nat 2 13 = 26.
Axiom add_26_1_eq_27 : add_nat 26 1 = 27.

Theorem n27_is_odd : odd 27.
prove exists k:set, nat_p k /\ 27 = add_nat (mul_nat 2 k) 1.
witness 13.
apply andI.
- exact nat_p_13.
- prove 27 = add_nat (mul_nat 2 13) 1.
  rewrite <- mul_2_13_eq_26.
  rewrite <- add_26_1_eq_27.
  exact eq_sym 27 (add_nat 26 1) add_26_1_eq_27.
Qed.

Theorem n27_not_even : ~even 27.
assume H27even: even 27.
claim H27odd: odd 27. exact n27_is_odd.
claim Hcontra: even 27 /\ odd 27.
  apply andI. exact H27even. exact H27odd.
exact even_not_odd 27 Hcontra.
Qed.

Axiom mul_9_3_eq_27 : mul_nat 9 3 = 27.
