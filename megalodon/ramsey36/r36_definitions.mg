Definition TwoRamseyProp : set -> set -> set -> prop
 := fun M N V =>
      forall R:set -> set -> prop,
        (forall x y, R x y -> R y x)
       -> ((exists X c= V, equip M X /\ (forall x y :e X, x <> y -> R x y))
        \/ (exists Y c= V, equip N Y /\ (forall x y :e Y, x <> y -> ~R x y))).

Definition is_graph : set -> (set -> set -> prop) -> prop :=
  fun V R => (forall x y, R x y -> R y x) /\ (forall x :e V, ~R x x).

Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x y z :e V, R x y -> R y z -> R x z -> False.

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => ~exists S c= V, equip k S /\ (forall x y :e S, x <> y -> ~R x y).

Definition neighbors : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {u :e V | R v u}.

Definition common_neighbors : set -> (set -> set -> prop) -> set -> set -> set :=
  fun V R u v => neighbors V R u :/\: neighbors V R v.

Definition degree : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R v d => equip d (neighbors V R v).

Definition k_regular : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall v :e V, degree V R v k.
