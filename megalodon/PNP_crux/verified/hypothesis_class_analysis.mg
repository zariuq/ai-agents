Variable m : set.
Axiom m_in_omega : m :e omega.
Axiom m_large : 2 :e m.

Definition log_m : set := Eps_i (fun k => k :e omega /\ exp_nat 2 k c= m /\ m :e exp_nat 2 (ordsucc k)).

Definition input_dimension : set := log_m.

Definition circuit_size : set := mul_nat log_m log_m.

Definition hypothesis_class_size_exponent : set := mul_nat circuit_size (log_m).

Definition log_H : set := hypothesis_class_size_exponent.

Definition training_samples : set := m.

Definition ERM_generalization_condition : prop :=
  log_H :e training_samples.

Theorem erm_analysis :
  log_H = mul_nat (mul_nat log_m log_m) log_m.
Admitted.

Definition polylog_hypothesis_bound : set -> prop := fun H_size =>
  exists c :e omega, H_size c= exp_nat log_m c.

Theorem log_H_is_polylog :
  polylog_hypothesis_bound (exp_nat 2 log_H).
Admitted.

Definition generalization_error_squared : set :=
  Eps_i (fun eps2 => eps2 :e omega /\ mul_nat eps2 training_samples = log_H).

Definition generalization_succeeds : prop :=
  log_H :e training_samples.

Theorem main_erm_bound :
  ERM_generalization_condition ->
  generalization_succeeds.
Admitted.

Definition critical_question : prop :=
  mul_nat (mul_nat log_m log_m) log_m :e m.

Theorem critical_bound_plausible :
  forall k : set, k :e omega ->
    exp_nat 2 k c= m ->
    mul_nat (mul_nat k k) k :e m.
Admitted.

Definition acc0_circuit_on_k_bits : set -> set -> set := fun k s =>
  exp_nat 2 (mul_nat k s).

Definition acc0_on_log_m : set := acc0_circuit_on_k_bits log_m circuit_size.

Theorem acc0_size_bound :
  acc0_on_log_m = exp_nat 2 (mul_nat log_m (mul_nat log_m log_m)).
Admitted.

Definition key_inequality : prop :=
  mul_nat log_m (mul_nat log_m log_m) :e m.

Theorem key_inequality_holds_for_large_m :
  16 c= m ->
  key_inequality.
Admitted.

Definition final_assessment : prop :=
  key_inequality -> generalization_succeeds.

Theorem hypothesis_class_concern_ANALYZED :
  final_assessment.
Admitted.

