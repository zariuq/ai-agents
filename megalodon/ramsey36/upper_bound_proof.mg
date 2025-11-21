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

Definition is_good_36 : set -> (set -> set -> prop) -> prop :=
  fun V R => triangle_free V R /\ no_k_indep V R 6.

Definition neighborhood : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {u :e V | R v u}.

Definition degree : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => Sep V (R v).

Definition max_degree_le : set -> (set -> set -> prop) -> set -> prop :=
  fun V R d => forall v :e V, degree V R v c= d.

Theorem upper_bound : TwoRamseyProp 3 6 18.
let R.
assume Rsym: forall x y, R x y -> R y x.
prove (exists X, X c= 18 /\ equip 3 X /\ (forall x :e X, forall y :e X, x <> y -> R x y))
   \/ (exists Y, Y c= 18 /\ equip 6 Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y)).
Admitted.
