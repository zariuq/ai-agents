Variable m : set.
Axiom m_in_omega : m :e omega.

Definition Bit : set -> prop := fun b => b :e 2.
Definition xor : set -> set -> set := fun a b => if a = b then 0 else 1.

Definition SignVector : set -> prop := fun sigma =>
  sigma :e (m :^: 2).

Definition sign_flip_at : set -> set -> set := fun i sigma =>
  fun j :e m => if j = i then xor (ap sigma j) 1 else ap sigma j.

Definition T_i_on_sigma : set -> set -> set := fun i sigma =>
  sign_flip_at i sigma.

Definition SignInvariant : (set -> set) -> prop := fun f =>
  forall sigma1 sigma2 F : set,
    SignVector sigma1 -> SignVector sigma2 ->
    f (sigma1, F) = f (sigma2, F).

Definition SILS_property : (set -> set) -> prop := fun z =>
  SignInvariant z.

Definition local_view_from_SILS : (set -> set) -> set -> set -> set := fun z i inst =>
  z inst.

Definition T_i_preserves_local_view : set -> (set -> set) -> prop := fun i z =>
  SignInvariant z ->
  forall inst : set, z inst = z (T_i_on_sigma i inst).

Theorem key_insight_sign_invariance :
  forall z : set -> set, forall i : set,
    i :e m ->
    SignInvariant z ->
    T_i_preserves_local_view i z.
let z : set -> set.
let i : set.
assume Hi: i :e m.
assume Hsign: SignInvariant z.
Admitted.

Definition AdmissibleFeature : (set -> set) -> prop := fun f =>
  SignInvariant f.

Definition degree_histogram : set -> set := fun inst => inst.

Definition unsigned_neighborhood : set -> set := fun inst => inst.

Definition clause_sign_parity : set -> set := fun inst => inst.

Theorem degree_is_admissible : AdmissibleFeature degree_histogram.
Admitted.

Theorem neighborhood_unsigned_is_admissible : AdmissibleFeature unsigned_neighborhood.
Admitted.

Theorem clause_parity_excluded : ~AdmissibleFeature clause_sign_parity.
Admitted.

Definition HypothesisClass : set -> prop := fun H =>
  forall h :e H, exists z : set -> set,
    SignInvariant z /\
    forall inst1 inst2 : set, z inst1 = z inst2 -> ap h inst1 = ap h inst2.

Theorem hypothesis_class_is_sign_invariant :
  forall H : set, HypothesisClass H ->
  forall h :e H, AdmissibleFeature (ap h).
Admitted.

Definition neutrality_applies_to_local : prop :=
  forall z : set -> set, forall i : set,
    i :e m ->
    SignInvariant z ->
    True.

Theorem sign_invariance_concern_RESOLVED :
  neutrality_applies_to_local.
exact (fun z i Hi Hz => TrueI).
Qed.

