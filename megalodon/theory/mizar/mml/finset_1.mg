Theorem finite_Empty : finite Empty.
prove exists n :e omega, equip Empty n.
witness 0.
apply andI.
- exact nat_p_omega 0 nat_0.
- exact equip_ref Empty.
Qed.

Theorem finite_equip_tra : forall X Y:set, finite X -> equip X Y -> finite Y.
let X Y.
assume HfX: finite X.
assume HeqXY: equip X Y.
prove exists n :e omega, equip Y n.
apply HfX.
let n. assume Hn: n :e omega /\ equip X n.
claim Hn_omega: n :e omega.
  exact andEL (n :e omega) (equip X n) Hn.
claim HeqXn: equip X n.
  exact andER (n :e omega) (equip X n) Hn.
witness n.
apply andI.
- exact Hn_omega.
- prove equip Y n.
  claim HeqYX: equip Y X.
    exact equip_sym X Y HeqXY.
  exact equip_tra Y X n HeqYX HeqXn.
Qed.

Theorem nat_finite : forall n:set, nat_p n -> finite n.
let n.
assume Hn: nat_p n.
prove exists m :e omega, equip n m.
witness n.
apply andI.
- exact nat_p_omega n Hn.
- exact equip_ref n.
Qed.

Theorem finite_6 : finite 6.
exact nat_finite 6 nat_6.
Qed.

Theorem finite_5 : finite 5.
exact nat_finite 5 nat_5.
Qed.

Theorem finite_4 : finite 4.
exact nat_finite 4 nat_4.
Qed.

Theorem finite_3 : finite 3.
exact nat_finite 3 nat_3.
Qed.

Theorem finite_2 : finite 2.
exact nat_finite 2 nat_2.
Qed.

Theorem finite_1 : finite 1.
exact nat_finite 1 nat_1.
Qed.

Theorem finset_compiles : True.
exact TrueI.
Qed.
