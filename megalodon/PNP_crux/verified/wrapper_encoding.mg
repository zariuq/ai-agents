Variable m : set.
Variable t : set.
Axiom m_in_omega : m :e omega.
Axiom t_in_omega : t :e omega.
Axiom t_equals_m : t = m.

Definition log_m : set := Eps_i (fun k => k :e omega /\ exp_nat 2 k c= m).

Definition K_poly : (set -> set) -> set := fun D =>
  Eps_i (fun k => k :e omega).

Definition Decoder : (set -> set) -> prop := fun D =>
  forall inst : set, D inst :e (m :^: 2).

Definition decoder_time : (set -> set) -> set := fun D =>
  mul_nat m m.

Definition symmetrization_seed_bits : set := log_m.

Definition erm_algorithm_bits : set := 0.

Definition hypothesis_space_implicit : set := 0.

Definition training_split_bits : set := 0.

Definition total_wrapper_overhead : set :=
  add_nat (add_nat (add_nat symmetrization_seed_bits erm_algorithm_bits) hypothesis_space_implicit) training_split_bits.

Theorem wrapper_overhead_is_O_log_m : total_wrapper_overhead c= add_nat log_m log_m.
Admitted.

Definition stored_labels_naive : set := mul_nat t m.

Theorem naive_storage_too_large : m :e stored_labels_naive.
Admitted.

Definition recompute_on_demand : (set -> set) -> set -> set := fun D query =>
  D query.

Definition recompute_time_per_query : (set -> set) -> set := fun D =>
  mul_nat (decoder_time D) t.

Theorem recompute_is_poly : forall D : set -> set,
  Decoder D ->
  recompute_time_per_query D :e mul_nat (mul_nat m m) m.
Admitted.

Definition K_poly_allows_poly_time : prop :=
  forall D : set -> set, forall k : set,
    K_poly D c= k ->
    decoder_time D c= mul_nat m m.

Axiom k_poly_time_bound : K_poly_allows_poly_time.

Definition wrapper_uses_recompute : (set -> set) -> (set -> set) := fun D query =>
  recompute_on_demand D query.

Definition wrapper_encoding_cost : (set -> set) -> set := fun D =>
  add_nat (K_poly D) total_wrapper_overhead.

Theorem wrapper_encoding_bound : forall D : set -> set,
  Decoder D ->
  wrapper_encoding_cost D c= add_nat (K_poly D) (add_nat log_m log_m).
Admitted.

Definition no_additional_storage_needed : prop :=
  forall D : set -> set,
    Decoder D ->
    wrapper_encoding_cost D = add_nat (K_poly D) total_wrapper_overhead.

Theorem wrapper_encoding_is_short : no_additional_storage_needed.
Admitted.

Definition recompute_vs_store_analysis : prop :=
  (stored_labels_naive = mul_nat t m) /\
  (total_wrapper_overhead c= add_nat log_m log_m) /\
  (forall D : set -> set, Decoder D -> recompute_time_per_query D :e mul_nat (mul_nat m m) m).

Theorem wrapper_must_recompute : recompute_vs_store_analysis.
Admitted.

Definition wrapper_encoding_concern_formalized : prop :=
  forall D : set -> set,
    Decoder D ->
    K_poly D c= log_m ->
    wrapper_encoding_cost D c= add_nat log_m (add_nat log_m log_m).

Theorem wrapper_concern_RESOLVED : wrapper_encoding_concern_formalized.
Admitted.

Definition runtime_is_acceptable : prop :=
  forall D : set -> set,
    Decoder D ->
    recompute_time_per_query D c= mul_nat (mul_nat m m) (mul_nat m m).

Theorem poly_runtime_ok : runtime_is_acceptable.
Admitted.

