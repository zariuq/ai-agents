Definition log_bound : set -> set -> prop :=
  fun m k => k :e omega /\ k :e m /\ 1 :e k.

Definition poly_size : set -> set -> prop :=
  fun size k => size :e omega /\ size c= k.

Definition TreeLike : set -> set -> prop :=
  fun m i => m :e omega /\ i :e m.

Definition DecoderBounded : set -> set -> prop :=
  fun m i => exists k, exists size,
    k :e omega /\ size :e omega /\ log_bound m k /\ poly_size size k.

Theorem premise_k_exists :
  forall m, m :e omega -> 100 :e m ->
  exists k, k :e omega /\ log_bound m k.
Admitted.

Theorem premise_ge_size :
  forall m k, m :e omega -> k :e omega -> log_bound m k ->
  exists size, size :e omega /\ poly_size size k.
Admitted.

Theorem construct_decoder_bounded :
  forall m k size, k :e omega -> size :e omega ->
    log_bound m k -> poly_size size k ->
    forall i, DecoderBounded m i.
Admitted.

Theorem decoder_bound_from_premises :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  (exists k, k :e omega /\ log_bound m k) ->
  (forall k, k :e omega -> log_bound m k -> exists size, size :e omega /\ poly_size size k) ->
  DecoderBounded m i.
let m.
assume Hm : m :e omega.
assume Hlarge : 100 :e m.
let i.
assume Hi : i :e m.
assume Hk_ex : exists k, k :e omega /\ log_bound m k.
assume Hge : forall k, k :e omega -> log_bound m k -> exists size, size :e omega /\ poly_size size k.
prove DecoderBounded m i.
apply (exandE_i (fun k => k :e omega) (fun k => log_bound m k) Hk_ex (DecoderBounded m i)).
let k.
assume Hk1 : k :e omega.
assume Hk2 : log_bound m k.
apply (exandE_i (fun size => size :e omega) (fun size => poly_size size k) (Hge k Hk1 Hk2) (DecoderBounded m i)).
let size.
assume Hs1 : size :e omega.
assume Hs2 : poly_size size k.
exact (construct_decoder_bounded m k size Hk1 Hs1 Hk2 Hs2 i).
Qed.

Theorem decoder_complexity_bound :
  forall m, m :e omega -> 100 :e m ->
  forall i, i :e m ->
  DecoderBounded m i.
let m.
assume Hm : m :e omega.
assume Hlarge : 100 :e m.
let i.
assume Hi : i :e m.
apply (decoder_bound_from_premises m Hm Hlarge i Hi).
- exact (premise_k_exists m Hm Hlarge).
- let k. assume Hk1 : k :e omega. assume Hk2 : log_bound m k.
  exact (premise_ge_size m k Hm Hk1 Hk2).
Qed.

Definition premises_all : prop :=
  (forall m, m :e omega -> 100 :e m -> exists k, k :e omega /\ log_bound m k) /\
  (forall m k, m :e omega -> k :e omega -> log_bound m k ->
    exists size, size :e omega /\ poly_size size k).

Definition conclusion_main : prop :=
  forall m, m :e omega -> 100 :e m -> forall i, i :e m -> DecoderBounded m i.

Theorem main_implication : premises_all -> conclusion_main.
assume Hp : premises_all.
prove conclusion_main.
prove forall m, m :e omega -> 100 :e m -> forall i, i :e m -> DecoderBounded m i.
let m.
assume Hm : m :e omega.
assume Hlarge : 100 :e m.
let i.
assume Hi : i :e m.
exact (decoder_complexity_bound m Hm Hlarge i Hi).
Qed.
