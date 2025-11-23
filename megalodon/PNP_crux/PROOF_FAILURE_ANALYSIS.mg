Definition log_bound : set -> set -> prop :=
  fun m k => k :e omega /\ k :e m /\ 1 :e k.

Definition poly_size : set -> set -> prop :=
  fun size k => size :e omega /\ size c= k.

Definition exp_size : set -> set -> prop :=
  fun size k => size :e omega.

Definition NeighborhoodSize : set -> set -> set -> prop :=
  fun m k size => m :e omega /\ k :e omega /\ size :e omega.

Definition DecoderCircuitPolyLog : set -> set -> prop :=
  fun m circuit_size => m :e omega /\ circuit_size :e omega /\
    exists k, log_bound m k /\ poly_size circuit_size k.

Definition DecoderCircuitPoly : set -> set -> prop :=
  fun m circuit_size => m :e omega /\ circuit_size :e omega /\
    circuit_size c= m.

Theorem gap1_xor_fails :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  False.
Admitted.

Theorem gap2_up_fails :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  False.
Admitted.

Theorem gap3_neighborhood_exponential :
  forall m k d : set,
  m :e omega -> k :e omega -> d :e omega ->
  log_bound m k ->
  2 :e d ->
  exists size, NeighborhoodSize m k size /\ exp_size size k.
Admitted.

Theorem gap3_implication :
  forall m k d size : set,
  m :e omega -> k :e omega -> d :e omega -> size :e omega ->
  log_bound m k ->
  NeighborhoodSize m k size ->
  exp_size size k ->
  DecoderCircuitPoly m size.
Admitted.

Theorem critical_gap :
  forall m, m :e omega -> 100 :e m ->
  (forall circuit_size, DecoderCircuitPolyLog m circuit_size -> False) \/
  (forall i, i :e m -> False).
Admitted.

Definition proof_requirements : prop :=
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  exists circuit_size, DecoderCircuitPolyLog m circuit_size.

Definition proof_failure : prop :=
  forall m, m :e omega -> 100 :e m ->
  exists d, 2 :e d /\
  forall k, log_bound m k ->
  exists size, NeighborhoodSize m k size /\ exp_size size k.

Theorem main_failure :
  proof_failure -> (proof_requirements -> False).
assume Hfail : proof_failure.
assume Hreq : proof_requirements.
prove False.
Admitted.
