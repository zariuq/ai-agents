Theorem nat_p_4 : nat_p 4.
exact nat_ordsucc 3 (nat_ordsucc 2 nat_2).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 (nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8
      (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 nat_p_4)))))))).
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13 nat_p_13))).
Qed.

Theorem nat_13_in_14 : 13 :e 14.
exact ordsuccI2 13.
Qed.

Theorem nat_14_not_in_14 : 14 /:e 14.
assume H: 14 :e 14.
exact In_irref 14 H.
Qed.

Theorem nat_4_in_17 : 4 :e 17.
prove 4 :e ordsucc 16.
apply ordsuccI1 16 4.
prove 4 :e 16.
apply ordsuccI1 15 4.
prove 4 :e 15.
apply ordsuccI1 14 4.
prove 4 :e 14.
apply ordsuccI1 13 4.
prove 4 :e 13.
apply ordsuccI1 12 4.
prove 4 :e 12.
apply ordsuccI1 11 4.
prove 4 :e 11.
apply ordsuccI1 10 4.
prove 4 :e 10.
apply ordsuccI1 9 4.
prove 4 :e 9.
apply ordsuccI1 8 4.
prove 4 :e 8.
apply ordsuccI1 7 4.
prove 4 :e 7.
apply ordsuccI1 6 4.
prove 4 :e 6.
apply ordsuccI1 5 4.
exact ordsuccI2 4.
Qed.

Theorem nat_4_subset_17 : 4 c= 17.
exact nat_trans 17 nat_p_17 4 nat_4_in_17.
Qed.

Theorem nat_lt_14_le_13 : forall g:set,
  nat_p g ->
  g :e 14 ->
  g c= 13.
let g.
assume Hg: nat_p g.
assume Hg14: g :e 14.
prove g c= 13.
let x. assume Hx: x :e g.
prove x :e 13.
apply ordsuccE 13 g Hg14.
- assume Hg13: g :e 13.
  exact nat_trans 13 nat_p_13 g Hg13 x Hx.
- assume Hg_eq: g = 13.
  rewrite <- Hg_eq.
  exact Hx.
Qed.

Theorem ordinal_theory_compiles : True.
exact TrueI.
Qed.
