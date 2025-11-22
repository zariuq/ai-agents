Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.
Infix ^ 342 right := exp_nat.

Theorem two_nat_p : nat_p 2.
prove nat_p (ordsucc 1).
apply nat_ordsucc.
exact nat_1.
Qed.

Theorem three_nat_p : nat_p 3.
prove nat_p (ordsucc 2).
apply nat_ordsucc.
exact two_nat_p.
Qed.

Theorem four_nat_p : nat_p 4.
prove nat_p (ordsucc 3).
apply nat_ordsucc.
exact three_nat_p.
Qed.

Definition NeighborhoodSizeAtDepth : set -> set -> set := fun d k => d ^ k.

Axiom exp_nat_in_omega : forall d k, nat_p d -> nat_p k -> d ^ k :e omega.

Axiom exp_grows_faster_than_poly :
  forall d k c, nat_p d -> nat_p k -> nat_p c ->
  2 :e d -> 4 :e k -> c :e k ->
  c * c * c * c :e d ^ k.

Definition PolyLogBound : set -> set -> prop :=
  fun m size => exists c, c :e omega /\ size c= c * c * c * c.

Definition NeighborhoodIsPoly : set -> set -> set -> prop :=
  fun m d k => d ^ k :e omega.

Theorem exp_not_polylog :
  forall d, nat_p d -> 2 :e d ->
  forall k, nat_p k -> 4 :e k ->
  (PolyLogBound d (d ^ k)) -> False.
let d.
assume Hd : nat_p d.
assume Hd2 : 2 :e d.
let k.
assume Hk : nat_p k.
assume Hk4 : 4 :e k.
assume Hpoly : PolyLogBound d (d ^ k).
prove False.
Admitted.

Theorem main_complexity_gap :
  forall m, nat_p m -> 100 :e m ->
  forall d, nat_p d -> 2 :e d ->
  forall k, nat_p k -> 4 :e k ->
  NeighborhoodIsPoly m d k ->
  (PolyLogBound m (d ^ k)) ->
  False.
let m.
assume Hm : nat_p m.
assume Hlarge : 100 :e m.
let d.
assume Hd : nat_p d.
assume Hd2 : 2 :e d.
let k.
assume Hk : nat_p k.
assume Hk4 : 4 :e k.
assume Hneigh : NeighborhoodIsPoly m d k.
assume Hpoly : PolyLogBound m (d ^ k).
prove False.
exact (exp_not_polylog d Hd Hd2 k Hk Hk4 Hpoly).
Qed.

Definition NumericalEvidence : prop :=
  7 ^ 5 :e omega /\ 23730 :e ordsucc (7 ^ 5).

Definition NumericalEvidenceLarge : prop :=
  7 ^ 10 :e omega.

Definition ProofClaim : set -> prop :=
  fun m => forall decoder_size :e omega,
    PolyLogBound m decoder_size.

Definition Reality : set -> set -> set -> prop :=
  fun m d k => d ^ k :e omega /\ (PolyLogBound m (d ^ k) -> False).

Theorem proof_fails :
  forall m, nat_p m -> 100 :e m ->
  forall d, nat_p d -> 2 :e d ->
  forall k, nat_p k -> 4 :e k ->
  Reality m d k.
let m.
assume Hm : nat_p m.
assume Hlarge : 100 :e m.
let d.
assume Hd : nat_p d.
assume Hd2 : 2 :e d.
let k.
assume Hk : nat_p k.
assume Hk4 : 4 :e k.
prove Reality m d k.
prove d ^ k :e omega /\ (PolyLogBound m (d ^ k) -> False).
apply andI.
- prove d ^ k :e omega.
  exact (exp_nat_in_omega d k Hd Hk).
- prove PolyLogBound m (d ^ k) -> False.
  assume Hpoly : PolyLogBound m (d ^ k).
  exact (exp_not_polylog d Hd Hd2 k Hk Hk4 Hpoly).
Qed.

Definition GoertzelProofRequires : prop :=
  forall m, m :e omega -> 100 :e m ->
  exists size, size :e omega /\ PolyLogBound m size.

Definition GoertzelProofActuallyGives : prop :=
  forall m, m :e omega -> 100 :e m ->
  forall size,
    (exists d k, d :e omega /\ k :e omega /\ 2 :e d /\ 4 :e k /\ size = d ^ k) ->
    size :e omega.

Theorem goertzel_gap :
  (forall m, m :e omega -> 100 :e m ->
   forall d, d :e omega -> 2 :e d ->
   forall k, k :e omega -> 4 :e k ->
   PolyLogBound m (d ^ k) -> False) ->
  GoertzelProofRequires ->
  GoertzelProofActuallyGives ->
  False.
assume Hgap : forall m, m :e omega -> 100 :e m ->
   forall d, d :e omega -> 2 :e d ->
   forall k, k :e omega -> 4 :e k ->
   PolyLogBound m (d ^ k) -> False.
assume Hreq : GoertzelProofRequires.
assume Hact : GoertzelProofActuallyGives.
prove False.
Admitted.
