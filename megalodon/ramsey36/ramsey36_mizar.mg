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
       -> ((exists X, X c= V /\ equip M X /\ (forall x :e X, forall y :e X, x <> y -> R x y))
        \/ (exists Y, Y c= V /\ equip N Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y))).

Definition Adj17 : set -> set -> prop :=
  fun i j =>
    (i = 0 /\ (j = 9 \/ j = 14 \/ j = 15 \/ j = 16)) \/
    (i = 1 /\ (j = 7 \/ j = 11 \/ j = 13 \/ j = 16)) \/
    (i = 2 /\ (j = 8 \/ j = 10 \/ j = 12 \/ j = 15)) \/
    (i = 3 /\ (j = 6 \/ j = 8 \/ j = 13 \/ j = 15 \/ j = 16)) \/
    (i = 4 /\ (j = 5 \/ j = 7 \/ j = 12 \/ j = 14 \/ j = 16)) \/
    (i = 5 /\ (j = 4 \/ j = 9 \/ j = 10 \/ j = 11 \/ j = 13)) \/
    (i = 6 /\ (j = 3 \/ j = 10 \/ j = 11 \/ j = 12 \/ j = 14)) \/
    (i = 7 /\ (j = 1 \/ j = 4 \/ j = 9 \/ j = 10 \/ j = 15)) \/
    (i = 8 /\ (j = 2 \/ j = 3 \/ j = 9 \/ j = 11 \/ j = 14)) \/
    (i = 9 /\ (j = 0 \/ j = 5 \/ j = 7 \/ j = 8 \/ j = 12)) \/
    (i = 10 /\ (j = 2 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 16)) \/
    (i = 11 /\ (j = 1 \/ j = 5 \/ j = 6 \/ j = 8 \/ j = 15)) \/
    (i = 12 /\ (j = 2 \/ j = 4 \/ j = 6 \/ j = 9 \/ j = 13)) \/
    (i = 13 /\ (j = 1 \/ j = 3 \/ j = 5 \/ j = 12 \/ j = 14)) \/
    (i = 14 /\ (j = 0 \/ j = 4 \/ j = 6 \/ j = 8 \/ j = 13)) \/
    (i = 15 /\ (j = 0 \/ j = 2 \/ j = 3 \/ j = 7 \/ j = 11)) \/
    (i = 16 /\ (j = 0 \/ j = 1 \/ j = 3 \/ j = 4 \/ j = 10)).

Theorem Adj17_sym : forall i j, Adj17 i j -> Adj17 j i.
Admitted.

Theorem Adj17_triangle_free : triangle_free 17 Adj17.
Admitted.

Theorem Adj17_no_6_indep : no_k_indep 17 Adj17 6.
Admitted.

Theorem lower_bound : ~TwoRamseyProp 3 6 17.
Admitted.

Theorem upper_bound : TwoRamseyProp 3 6 18.
Admitted.

Theorem Ramsey_3_6_eq_18 : TwoRamseyProp 3 6 18 /\ ~TwoRamseyProp 3 6 17.
apply andI.
- exact upper_bound.
- exact lower_bound.
Qed.
