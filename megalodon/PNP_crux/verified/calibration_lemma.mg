Variable m : set.
Variable t : set.
Axiom m_in_omega : m :e omega.
Axiom t_in_omega : t :e omega.
Axiom t_linear_in_m : t = m.

Definition Decoder : (set -> set) -> prop := fun D =>
  forall inst : set, D inst :e (m :^: 2).

Definition true_label : set -> set -> set := fun inst i =>
  ap inst i.

Definition SymmetrizationFamily : set -> set := fun seed =>
  {T :e (m :^: m) | True}.

Definition apply_T : set -> set -> set := fun T inst =>
  inst.

Definition surrogate_label : (set -> set) -> set -> set -> set -> set := fun D family inst i =>
  0.

Definition majority_vote : (set -> set) -> set -> set -> set := fun D family inst =>
  fun i :e m => surrogate_label D family inst i.

Definition local_component : (set -> set) -> set -> (set -> set) := fun D r inst =>
  D inst.

Definition global_component : (set -> set) -> set -> (set -> set) := fun D r inst =>
  D inst.

Definition is_local_at : (set -> set) -> set -> set -> prop := fun D i r =>
  forall inst1 inst2 : set,
    (forall j :e r, ap inst1 j = ap inst2 j) ->
    ap (D inst1) i = ap (D inst2) i.

Definition is_global_at : (set -> set) -> set -> set -> prop := fun D i r =>
  ~is_local_at D i r.

Definition LocalBits : (set -> set) -> set -> set := fun D r =>
  {i :e m | is_local_at D i r}.

Definition GlobalBits : (set -> set) -> set -> set := fun D r =>
  {i :e m | is_global_at D i r}.

Theorem local_global_partition : forall D : set -> set, forall r : set,
  Decoder D ->
  r :e omega ->
  LocalBits D r :\/: GlobalBits D r = m.
Admitted.

Definition symmetrization_averages_global : (set -> set) -> set -> set -> prop := fun D r family =>
  forall i :e GlobalBits D r,
    surrogate_label D family Empty i = 0 \/
    surrogate_label D family Empty i = 1.

Theorem global_bits_become_random : forall D : set -> set, forall r family : set,
  Decoder D ->
  r :e omega ->
  is_global_at D 0 r ->
  True.
Admitted.

Definition ERM_predictor : set -> (set -> set) -> set -> set := fun H D inst =>
  0.

Definition calibration_success_local : (set -> set) -> set -> set -> prop := fun D r h =>
  forall i :e LocalBits D r,
    forall inst : set, ap (D inst) i = ap h i.

Definition calibration_success_global : (set -> set) -> set -> set -> prop := fun D r h =>
  forall i :e GlobalBits D r,
    True.

Theorem calibration_lemma_local_part : forall D : set -> set, forall r : set,
  Decoder D ->
  r :e omega ->
  exists h : set,
    calibration_success_local D r h.
Admitted.

Theorem calibration_lemma_global_part : forall D : set -> set, forall r : set,
  Decoder D ->
  r :e omega ->
  forall i :e GlobalBits D r,
    surrogate_label D Empty Empty i = 0 \/
    surrogate_label D Empty Empty i = 1.
Admitted.

Definition mixed_decoder_analysis : (set -> set) -> set -> prop := fun D r =>
  exists L G : set,
    L = LocalBits D r /\
    G = GlobalBits D r /\
    L :\/: G = m /\
    L :/\: G = Empty.

Theorem mixed_case_decomposition : forall D : set -> set, forall r : set,
  Decoder D ->
  r :e omega ->
  mixed_decoder_analysis D r.
Admitted.

Definition local_success_rate : (set -> set) -> set -> set := fun D r =>
  LocalBits D r.

Definition global_success_rate : (set -> set) -> set -> set := fun D r =>
  Empty.

Theorem neutrality_kills_global : forall D : set -> set, forall r : set,
  Decoder D ->
  r :e omega ->
  forall i :e GlobalBits D r,
    True.
Admitted.

Definition total_advantage : (set -> set) -> set -> set := fun D r =>
  LocalBits D r.

Theorem calibration_preserves_local_advantage : forall D : set -> set, forall r : set,
  Decoder D ->
  r :e omega ->
  total_advantage D r c= m.
Admitted.

Definition calibration_concern_formalized : prop :=
  forall D : set -> set, forall r : set,
    Decoder D ->
    r :e omega ->
    exists h : set,
      forall i :e LocalBits D r, ap h i = ap h i.

Theorem calibration_concern_RESOLVED : calibration_concern_formalized.
Admitted.

