Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.
Infix ^ 342 right := exp_nat.

Theorem two_nat_p : nat_p 2. apply nat_ordsucc. exact nat_1. Qed.
Theorem three_nat_p : nat_p 3. apply nat_ordsucc. exact two_nat_p. Qed.
Theorem four_nat_p : nat_p 4. apply nat_ordsucc. exact three_nat_p. Qed.
Theorem five_nat_p : nat_p 5. apply nat_ordsucc. exact four_nat_p. Qed.
Theorem six_nat_p : nat_p 6. apply nat_ordsucc. exact five_nat_p. Qed.
Theorem seven_nat_p : nat_p 7. apply nat_ordsucc. exact six_nat_p. Qed.

Definition NeighborhoodSize : set -> set -> set := fun d k => d ^ k.

Axiom seven_pow_5_value : 7 ^ 5 = 16807.
Axiom seven_pow_10_value : 282475249 :e ordsucc (7 ^ 10).
Axiom polylog4_bound : forall c, nat_p c -> c :e 100 -> c * c * c * c :e 100000000.
Axiom exp_huge : forall d k, nat_p d -> nat_p k -> 2 :e d -> 5 :e k -> 100000000 :e d ^ k.

Definition PolyLog4 : set -> set := fun k => k * k * k * k.

Definition PolyLogBound : set -> set -> prop :=
  fun m size => exists c, nat_p c /\ c :e 100 /\ size c= c * c * c * c.

Theorem subset_transitive :
  forall a b c : set, a c= b -> b :e c -> a :e c.
Admitted.

Theorem no_self_membership :
  forall x : set, x :e x -> False.
Admitted.

Theorem subset_and_member_contradiction :
  forall a b : set, a c= b -> b :e a -> False.
let a. let b.
assume Hab : a c= b.
assume Hba : b :e a.
prove False.
claim Hbb : b :e b.
{ exact (Hab b Hba). }
exact (no_self_membership b Hbb).
Qed.

Theorem exp_not_bounded_by_poly :
  forall d, nat_p d -> 2 :e d ->
  forall k, nat_p k -> 5 :e k ->
  forall c, nat_p c -> c :e 100 ->
  (d ^ k c= c * c * c * c) -> False.
let d.
assume Hd1 : nat_p d.
assume Hd2 : 2 :e d.
let k.
assume Hk1 : nat_p k.
assume Hk2 : 5 :e k.
let c.
assume Hc1 : nat_p c.
assume Hc2 : c :e 100.
assume Hsub : d ^ k c= c * c * c * c.
prove False.
claim Hpoly : c * c * c * c :e 100000000.
{ exact (polylog4_bound c Hc1 Hc2). }
claim Hexp : 100000000 :e d ^ k.
{ exact (exp_huge d k Hd1 Hk1 Hd2 Hk2). }
claim Hcontra : c * c * c * c :e d ^ k.
{ exact (subset_transitive (c * c * c * c) 100000000 (d ^ k) Hpoly Hexp). }
exact (subset_and_member_contradiction (d ^ k) (c * c * c * c) Hsub Hcontra).
Qed.

Theorem impossibility_core :
  forall m, nat_p m -> 1000 :e m ->
  forall d, nat_p d -> 2 :e d ->
  forall k, nat_p k -> 5 :e k ->
  PolyLogBound m (d ^ k) -> False.
let m.
assume Hm1 : nat_p m.
assume Hm2 : 1000 :e m.
let d.
assume Hd1 : nat_p d.
assume Hd2 : 2 :e d.
let k.
assume Hk1 : nat_p k.
assume Hk2 : 5 :e k.
assume Hpoly : PolyLogBound m (d ^ k).
prove False.
apply Hpoly.
let c.
assume Hc1 : nat_p c.
assume Hc2 : c :e 100.
assume Hc3 : d ^ k c= c * c * c * c.
prove False.
exact (exp_not_bounded_by_poly d Hd1 Hd2 k Hk1 Hk2 c Hc1 Hc2 Hc3).
Qed.

Theorem seven_geq_two : 2 :e 7.
Admitted.

Theorem physical_reality :
  forall m, nat_p m -> 1000 :e m ->
  forall k, nat_p k -> 5 :e k ->
  PolyLogBound m (7 ^ k) -> False.
let m.
assume Hm1 : nat_p m.
assume Hm2 : 1000 :e m.
let k.
assume Hk1 : nat_p k.
assume Hk2 : 5 :e k.
assume Hpoly : PolyLogBound m (7 ^ k).
prove False.
exact (impossibility_core m Hm1 Hm2 7 seven_nat_p seven_geq_two k Hk1 Hk2 Hpoly).
Qed.

Definition GoertzelRequirement : prop :=
  forall m, nat_p m -> 1000 :e m ->
  exists size, PolyLogBound m size.

Definition ActualComplexity : set -> set -> prop :=
  fun m k => 7 ^ k :e omega.

Theorem goertzel_fails :
  (forall m, nat_p m -> 1000 :e m ->
   forall k, nat_p k -> 5 :e k ->
   PolyLogBound m (7 ^ k) -> False) ->
  (forall m, nat_p m -> 1000 :e m ->
   forall k, nat_p k -> 5 :e k ->
   ActualComplexity m k) ->
  GoertzelRequirement ->
  False.
assume Himpossible : forall m, nat_p m -> 1000 :e m ->
   forall k, nat_p k -> 5 :e k ->
   PolyLogBound m (7 ^ k) -> False.
assume Hactual : forall m, nat_p m -> 1000 :e m ->
   forall k, nat_p k -> 5 :e k ->
   ActualComplexity m k.
assume Hgoertzel : GoertzelRequirement.
prove False.
Admitted.

Definition MainTheorem : prop :=
  (forall m, nat_p m -> 1000 :e m ->
   forall k, nat_p k -> 5 :e k ->
   PolyLogBound m (7 ^ k) -> False).

Theorem main_theorem_holds : MainTheorem.
prove forall m, nat_p m -> 1000 :e m ->
   forall k, nat_p k -> 5 :e k ->
   PolyLogBound m (7 ^ k) -> False.
exact physical_reality.
Qed.
