Definition R : set := real.
Definition R_zero : set := 0.
Definition R_one : set := 1.
Definition R_plus : set -> set -> set := fun x y => x + y.
Definition R_mult : set -> set -> set := fun x y => x * y.
Definition R_leq : set -> set -> prop := fun x y => x <= y.
Definition R_minus : set -> set -> set := fun x y => x + - y.

Infix + 360 right := R_plus.
Infix * 355 right := R_mult.
Infix <= 490 := R_leq.

Axiom R_zero_In : R_zero :e R.
Axiom R_one_In : R_one :e R.
Axiom R_plus_clos : forall x y :e R, x + y :e R.
Axiom R_mult_clos : forall x y :e R, x * y :e R.
Axiom R_minus_clos : forall x y :e R, R_minus x y :e R.

Axiom R_leq_refl : forall x :e R, x <= x.
Axiom R_leq_trans : forall x y z :e R, x <= y -> y <= z -> x <= z.
Axiom R_leq_antisym : forall x y :e R, x <= y -> y <= x -> x = y.
Axiom R_zero_leq_one : R_zero <= R_one.
Axiom R_zero_leq_x_implies_plus_leq : forall x y :e R, R_zero <= y -> x <= x + y.

Axiom R_plus_comm : forall x y :e R, x + y = y + x.
Axiom R_plus_assoc : forall x y z :e R, x + (y + z) = (x + y) + z.
Axiom R_plus_zero : forall x :e R, x + R_zero = x.

Axiom R_minus_self : forall x :e R, R_minus x x = R_zero.
Axiom R_plus_minus : forall x y :e R, R_minus (x + y) y = x.
Axiom R_minus_plus_distr : forall x y z :e R, R_minus x (y + z) = R_minus (R_minus x y) z.
Axiom R_minus_eq_iff : forall x y :e R, x = R_minus R_one y <-> x + y = R_one.

Axiom R_leq_plus_r : forall x y z :e R, x <= y -> x + z <= y + z.
Axiom R_leq_plus_cancel : forall x y z :e R, x + z <= y + z -> x <= y.

Definition partial_sum : (set -> set) -> set -> set :=
  fun f n => Sum 0 n f.

Definition is_upper_bound : (set -> set) -> set -> prop :=
  fun f s => forall n :e omega, partial_sum f n <= s.

Definition is_least_upper_bound : (set -> set) -> set -> prop :=
  fun f s =>
    is_upper_bound f s
    /\ (forall t :e R, is_upper_bound f t -> s <= t).

Definition sum_nat : (set -> set) -> set :=
  fun f => Eps_i (fun s => s :e R /\ is_least_upper_bound f s).

Definition Disjoint : set -> set -> prop :=
  fun A B => A :/\: B = Empty.

Definition pairwise_disjoint : (set -> set) -> prop :=
  fun f => forall m n :e omega, m <> n -> Disjoint (f m) (f n).

Definition is_sigma_field : set -> set -> prop := is_sigma_algebra.


Definition is_probability_measure : set -> set -> (set -> set) -> prop :=
  fun Omega F P =>
    is_sigma_field Omega F
    /\ ((forall A :e F, P A :e R /\ R_zero <= P A)
    /\ (P Omega = R_one
    /\ (P Empty = R_zero
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         pairwise_disjoint f ->
         P (bigcup_nat f) = sum_nat (fun n => P (f n)))))).


Theorem prob_measure_is_sigma_field :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    is_sigma_field Omega F.
let Omega. let F. let P: set -> set.
assume H.
apply H.
assume Hsigma.
assume Hrest.
exact Hsigma.
Qed.

Theorem prob_empty_zero :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    P Empty = R_zero.
let Omega. let F. let P: set -> set.
assume H.
claim H_rest: (forall A :e F, P A :e R /\ R_zero <= P A) /\ (P Omega = R_one /\ (P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e R /\ R_zero <= P A) /\ (P Omega = R_one /\ (P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
claim H_rest2: P Omega = R_one /\ (P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))).
  exact andER (forall A :e F, P A :e R /\ R_zero <= P A) (P Omega = R_one /\ (P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) H_rest.
claim H_rest3: P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  exact andER (P Omega = R_one) (P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H_rest2.
exact andEL (P Empty = R_zero) (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))) H_rest3.
Qed.

Theorem prob_finite_additivity :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    Disjoint A B ->
    P (A :\/: B) = P A + P B.
let Omega. let F. let P: set -> set. let A. let B.
assume H. assume HA. assume HB. assume Hd.
admit.
Qed.

Theorem prob_monotone :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    A c= B ->
    P A <= P B.
let Omega. let F. let P: set -> set. let A. let B.
assume H. assume HA. assume HB. assume Hab.
admit.
Qed.

Theorem prob_complement :
  forall Omega F, forall P: set -> set, forall A,
    is_probability_measure Omega F P ->
    A :e F ->
    P (Omega :\: A) = R_minus R_one (P A).
let Omega. let F. let P: set -> set. let A.
assume H. assume HA.
admit.
Qed.

Theorem prob_union_bound :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    P (A :\/: B) <= P A + P B.
let Omega. let F. let P: set -> set. let A. let B.
assume H. assume HA. assume HB.
admit.
Qed.
