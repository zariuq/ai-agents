Definition triangle_free : set -> (set -> set -> prop) -> prop :=
  fun V R => forall x :e V, forall y :e V, forall z :e V, R x y -> R y z -> R x z -> False.

Definition is_indep_set : set -> (set -> set -> prop) -> set -> prop :=
  fun V R S => S c= V /\ (forall x :e S, forall y :e S, x <> y -> ~R x y).

Definition no_k_indep : set -> (set -> set -> prop) -> set -> prop :=
  fun V R k => forall S, S c= V -> equip k S -> ~is_indep_set V R S.

Definition TwoRamseyProp : set -> set -> set -> prop :=
  fun m n k => forall R:set -> set -> prop, (forall x y, R x y -> R y x) ->
    ((exists X, X c= k /\ equip m X /\ (forall x :e X, forall y :e X, x <> y -> R x y))
     \/ (exists Y, Y c= k /\ equip n Y /\ (forall x :e Y, forall y :e Y, x <> y -> ~R x y))).

Definition neighborhood : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {w :e V | R v w}.

Definition has_degree : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun V R v d => equip d (neighborhood V R v).

Definition is_5_regular : set -> (set -> set -> prop) -> prop :=
  fun V R => forall v :e V, has_degree V R v 5.

Definition GoodGraph : set -> (set -> set -> prop) -> prop :=
  fun V R =>
    (forall x y, R x y -> R y x) /\
    equip 18 V /\
    triangle_free V R /\
    no_k_indep V R 6.

Axiom Ramsey_3_5_eq_14 : TwoRamseyProp 3 5 14.

Axiom equip_refl : forall X, equip X X.

Theorem neighborhood_indep_in_triangle_free : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  forall v :e V,
    forall x :e neighborhood V R v, forall y :e neighborhood V R v, x <> y -> ~R x y.
let V. let R: set -> set -> prop.
assume Rsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
let x. assume Hx: x :e neighborhood V R v.
let y. assume Hy: y :e neighborhood V R v.
assume Hneq: x <> y.
assume Hxy: R x y.
prove False.
apply SepE V (fun w => R v w) x Hx.
assume HxV: x :e V.
assume Hvx: R v x.
apply SepE V (fun w => R v w) y Hy.
assume HyV: y :e V.
assume Hvy: R v y.
exact Htf v Hv x HxV y HyV Hvx Hxy Hvy.
Qed.

Theorem degree_upper_bound_from_R35 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  triangle_free V R ->
  forall v :e V,
    has_degree V R v 6 -> False.
let V. let R: set -> set -> prop.
assume Rsym: forall x y, R x y -> R y x.
assume Htf: triangle_free V R.
let v. assume Hv: v :e V.
assume Hdeg6: has_degree V R v 6.
prove False.
claim Hindep: forall x :e neighborhood V R v, forall y :e neighborhood V R v, x <> y -> ~R x y.
  exact neighborhood_indep_in_triangle_free V R Rsym Htf v Hv.
Admitted.

Theorem degree_lower_bound_4 : forall V:set, forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) ->
  equip 18 V ->
  no_k_indep V R 6 ->
  forall v :e V,
    ~(has_degree V R v 0) /\ ~(has_degree V R v 1) /\ ~(has_degree V R v 2) /\ ~(has_degree V R v 3).
Admitted.

Theorem claim1_degree_exactly_5 : forall V:set, forall R:set -> set -> prop,
  GoodGraph V R ->
  forall v :e V, has_degree V R v 5.
Admitted.

Theorem claim1_5_regularity : forall V:set, forall R:set -> set -> prop,
  GoodGraph V R ->
  is_5_regular V R.
let V. let R: set -> set -> prop.
assume HG: GoodGraph V R.
prove forall v :e V, has_degree V R v 5.
let v. assume Hv: v :e V.
exact claim1_degree_exactly_5 V R HG v Hv.
Qed.

Definition non_neighbor : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {w :e V | w <> v /\ ~R v w}.

Definition A_part : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {w :e non_neighbor V R v | exists u :e neighborhood V R v, R w u}.

Definition B_part : set -> (set -> set -> prop) -> set -> set :=
  fun V R v => {w :e non_neighbor V R v | forall u :e neighborhood V R v, ~R w u}.

Theorem claim2_partition_sizes : forall V:set, forall R:set -> set -> prop,
  GoodGraph V R ->
  forall v :e V,
    equip 5 (neighborhood V R v) /\
    equip 7 (A_part V R v) /\
    equip 5 (B_part V R v).
Admitted.

Theorem claim2_A_unique_neighbor : forall V:set, forall R:set -> set -> prop,
  GoodGraph V R ->
  forall v :e V,
    forall a :e A_part V R v, exists u :e neighborhood V R v, R a u /\
      forall u' :e neighborhood V R v, R a u' -> u' = u.
Admitted.

Theorem claim3_4cycle_exists : forall V:set, forall R:set -> set -> prop,
  GoodGraph V R ->
  exists a b c d,
    a :e V /\ b :e V /\ c :e V /\ d :e V /\
    a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
    R a b /\ R b c /\ R c d /\ R d a /\
    ~R a c /\ ~R b d.
Admitted.

Theorem final_counting_contradiction : forall V:set, forall R:set -> set -> prop,
  GoodGraph V R ->
  is_5_regular V R ->
  (exists a b c d,
    a :e V /\ b :e V /\ c :e V /\ d :e V /\
    a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
    R a b /\ R b c /\ R c d /\ R d a /\
    ~R a c /\ ~R b d) ->
  False.
Admitted.

Theorem final_contradiction : forall V:set, forall R:set -> set -> prop,
  GoodGraph V R ->
  False.
let V. let R: set -> set -> prop.
assume HG: GoodGraph V R.
claim H5reg: is_5_regular V R.
  exact claim1_5_regularity V R HG.
claim H4cycle: exists a b c d,
    a :e V /\ b :e V /\ c :e V /\ d :e V /\
    a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d /\
    R a b /\ R b c /\ R c d /\ R d a /\
    ~R a c /\ ~R b d.
  exact claim3_4cycle_exists V R HG.
exact final_counting_contradiction V R HG H5reg H4cycle.
Qed.

Theorem good_graph_contradiction : forall R:set -> set -> prop,
  (forall x y, R x y -> R y x) -> triangle_free 18 R -> no_k_indep 18 R 6 -> False.
let R: set -> set -> prop.
assume Rsym: forall x y, R x y -> R y x.
assume Htf: triangle_free 18 R.
assume Hno6: no_k_indep 18 R 6.
apply final_contradiction 18 R.
prove GoodGraph 18 R.
prove (forall x y, R x y -> R y x) /\ equip 18 18 /\ triangle_free 18 R /\ no_k_indep 18 R 6.
apply and4I.
- exact Rsym.
- exact equip_refl 18.
- exact Htf.
- exact Hno6.
Qed.
