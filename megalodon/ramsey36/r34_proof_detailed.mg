Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Definition TwoRamseyProp : set -> set -> set -> prop
 := fun M N V =>
      forall R:set -> set -> prop,
        (forall x y, R x y -> R y x)
       -> ((exists X c= V, equip M X /\ (forall x y :e X, x <> y -> R x y))
        \/ (exists Y c= V, equip N Y /\ (forall x y :e Y, x <> y -> ~R x y))).

Theorem nat_p_9 : nat_p 9.
exact nat_ordsucc 8 (nat_ordsucc 7 (nat_ordsucc 6 (nat_ordsucc 5
      (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2)))))).
Qed.

Theorem TwoRamseyProp_3_3_6 : TwoRamseyProp 3 3 6.
Admitted.

Theorem degree_upper_bound : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 9 R ->
  no_k_indep 9 R 4 ->
  forall v :e 9, forall N:set, N c= 9 ->
    (forall x :e N, R v x /\ x <> v) ->
    equip 4 N -> False.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 9 R.
assume Hno4: no_k_indep 9 R 4.
let v. assume Hv: v :e 9.
let N. assume HN9: N c= 9.
assume HNadj: forall x :e N, R v x /\ x <> v.
assume HN4: equip 4 N.
prove False.
apply Hno4 N HN9 HN4.
prove is_indep_set 9 R N.
prove N c= 9 /\ (forall x :e N, forall y :e N, x <> y -> ~R x y).
apply andI.
- exact HN9.
- prove forall x :e N, forall y :e N, x <> y -> ~R x y.
  let x. assume Hx: x :e N.
  let y. assume Hy: y :e N.
  assume Hneq: x <> y.
  prove ~R x y.
  claim HRvx: R v x. exact andEL (R v x) (x <> v) (HNadj x Hx).
  claim HRvy: R v y. exact andEL (R v y) (y <> v) (HNadj y Hy).
  assume HRxy: R x y.
  apply Htf x (HN9 x Hx) y (HN9 y Hy) v Hv HRxy (Hsym v y HRvy) (Hsym v x HRvx).
Qed.

Theorem degree_lower_bound : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free 9 R ->
  TwoRamseyProp 3 3 6 ->
  forall v :e 9,
  ~(exists N M:set,
     N c= 9 /\ M c= 9 /\
     (forall x :e N, R v x /\ x <> v) /\
     (forall x :e M, ~R v x /\ x <> v) /\
     (forall x :e 9, x <> v -> (x :e N \/ x :e M)) /\
     equip 2 N /\ equip 6 M).
Admitted.

Theorem TwoRamseyProp_3_4_9 : TwoRamseyProp 3 4 9.
let R: set -> set -> prop.
assume Hsym: forall x y, R x y -> R y x.
prove (exists X c= 9, equip 3 X /\ (forall x y :e X, x <> y -> R x y))
   \/ (exists Y c= 9, equip 4 Y /\ (forall x y :e Y, x <> y -> ~R x y)).
apply dnegI.
assume Hneg: ~((exists X c= 9, equip 3 X /\ (forall x y :e X, x <> y -> R x y))
             \/ (exists Y c= 9, equip 4 Y /\ (forall x y :e Y, x <> y -> ~R x y))).
prove False.
Admitted.
Qed.
