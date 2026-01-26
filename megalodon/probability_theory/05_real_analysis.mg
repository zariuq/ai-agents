Definition seq_real : (set -> set) -> prop :=
  fun f => forall n :e omega, f n :e real.

Definition seq_le : (set -> set) -> (set -> set) -> prop :=
  fun f g => forall n :e omega, f n <= g n.

Definition monotone_nondec : (set -> set) -> prop :=
  fun f => forall m n :e omega, m :e n -> f m <= f n.

Definition monotone_noninc : (set -> set) -> prop :=
  fun f => forall m n :e omega, m :e n -> f n <= f m.

Definition is_upper_bound_seq : (set -> set) -> set -> prop :=
  fun f s => forall n :e omega, f n <= s.

Definition is_lower_bound_seq : (set -> set) -> set -> prop :=
  fun f s => forall n :e omega, s <= f n.

Definition is_least_upper_bound_seq : (set -> set) -> set -> prop :=
  fun f s =>
    is_upper_bound_seq f s
    /\ (forall t :e real, is_upper_bound_seq f t -> s <= t).

Definition is_greatest_lower_bound_seq : (set -> set) -> set -> prop :=
  fun f s =>
    is_lower_bound_seq f s
    /\ (forall t :e real, is_lower_bound_seq f t -> t <= s).

Definition bounded_above : (set -> set) -> prop :=
  fun f => exists s :e real, is_upper_bound_seq f s.

Definition bounded_below : (set -> set) -> prop :=
  fun f => exists s :e real, is_lower_bound_seq f s.

Definition converges_to : (set -> set) -> set -> prop :=
  fun f l =>
    forall k :e omega, exists N :e omega,
      forall n :e omega, N :e n -> abs_SNo (f n + - l) < eps_ k.

Definition convergent : (set -> set) -> prop :=
  fun f => exists l :e real, converges_to f l.

Definition limit : (set -> set) -> set :=
  fun f => Eps_i (fun l => l :e real /\ converges_to f l).

Definition series_partial_sum : (set -> set) -> set -> set := partial_sum.

Definition series_sum : (set -> set) -> set := sum_nat.

Theorem partial_sum_0 :
  forall f : set -> set, partial_sum f 0 = f 0.
let f : set -> set.
claim Hdef: partial_sum f 0 =
  nat_primrec 0 (fun k r => if k :e 0 then 0 else f k + r) (ordsucc 0).
{ reflexivity. }
rewrite Hdef.
rewrite (nat_primrec_S 0 (fun k r => if k :e 0 then 0 else f k + r) 0 nat_0).
rewrite (nat_primrec_0 0 (fun k r => if k :e 0 then 0 else f k + r)).
rewrite (If_i_0 (0 :e 0) 0 (f 0 + 0) nIn_0_0).
rewrite (real_add_zero_r (f 0)).
reflexivity.
Qed.

Theorem partial_sum_succ :
  forall f : set -> set, forall n :e omega,
    partial_sum f (ordsucc n) = f (ordsucc n) + partial_sum f n.
let f : set -> set.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim Hdef: partial_sum f (ordsucc n) =
  nat_primrec 0 (fun k r => if k :e 0 then 0 else f k + r) (ordsucc (ordsucc n)).
{ reflexivity. }
rewrite Hdef.
rewrite (nat_primrec_S 0 (fun k r => if k :e 0 then 0 else f k + r) (ordsucc n) (nat_ordsucc n Hn_nat)).
claim Hdef2: nat_primrec 0 (fun k r => if k :e 0 then 0 else f k + r) (ordsucc n)
  = partial_sum f n.
{ reflexivity. }
rewrite Hdef2.
rewrite (If_i_0 (ordsucc n :e 0) 0 (f (ordsucc n) + partial_sum f n) (EmptyE (ordsucc n))).
reflexivity.
Qed.

Theorem lub_seq_is_upper_bound :
  forall f : set -> set, forall s,
    is_least_upper_bound_seq f s ->
    is_upper_bound_seq f s.
let f. let s.
assume H.
exact andEL (is_upper_bound_seq f s)
            (forall t :e real, is_upper_bound_seq f t -> s <= t)
            H.
Qed.

Theorem glb_seq_is_lower_bound :
  forall f : set -> set, forall s,
    is_greatest_lower_bound_seq f s ->
    is_lower_bound_seq f s.
let f. let s.
assume H.
exact andEL (is_lower_bound_seq f s)
            (forall t :e real, is_lower_bound_seq f t -> t <= s)
            H.
Qed.

Theorem least_upper_bound_seq_unique :
  forall f : set -> set,
  forall s t :e real,
    is_least_upper_bound_seq f s ->
    is_least_upper_bound_seq f t ->
    s = t.
let f.
let s.
assume Hs: s :e real.
let t.
assume Ht: t :e real.
assume Hs_lub. assume Ht_lub.
claim Hs_upper: is_upper_bound_seq f s.
  exact andEL (is_upper_bound_seq f s)
              (forall t0 :e real, is_upper_bound_seq f t0 -> s <= t0)
              Hs_lub.
claim Hs_min: forall t0 :e real, is_upper_bound_seq f t0 -> s <= t0.
  exact andER (is_upper_bound_seq f s)
              (forall t0 :e real, is_upper_bound_seq f t0 -> s <= t0)
              Hs_lub.
claim Ht_upper: is_upper_bound_seq f t.
  exact andEL (is_upper_bound_seq f t)
              (forall t0 :e real, is_upper_bound_seq f t0 -> t <= t0)
              Ht_lub.
claim Ht_min: forall t0 :e real, is_upper_bound_seq f t0 -> t <= t0.
  exact andER (is_upper_bound_seq f t)
              (forall t0 :e real, is_upper_bound_seq f t0 -> t <= t0)
              Ht_lub.
claim Hst: s <= t.
  exact Hs_min t Ht Ht_upper.
claim Hts: t <= s.
  exact Ht_min s Hs Hs_upper.
exact real_leq_antisym s Hs t Ht Hst Hts.
Qed.

Theorem converges_to_const :
  forall c :e real, converges_to (fun n:set => c) c.
let c.
assume Hc: c :e real.
let k.
assume Hk: k :e omega.
witness 0.
apply andI (0 :e omega) (forall n :e omega, 0 :e n -> abs_SNo ((fun n:set => c) n + - c) < eps_ k).
- exact nat_p_omega 0 nat_0.
- let n.
  assume Hn: n :e omega.
  assume H0n: 0 :e n.
  claim Habs: abs_SNo (c + - c) = 0.
  { rewrite (real_add_left_inv c). exact abs_SNo_0. }
  rewrite Habs.
  exact SNo_eps_pos k Hk.
Qed.

Theorem convergent_const :
  forall c :e real, exists l :e real, converges_to (fun n:set => c) l.
let c.
assume Hc: c :e real.
witness c.
apply andI (c :e real) (converges_to (fun n:set => c) c).
- exact Hc.
- exact converges_to_const c Hc.
Qed.

Theorem seq_real_const :
  forall c :e real, seq_real (fun n:set => c).
let c.
assume Hc: c :e real.
let n.
assume Hn: n :e omega.
exact Hc.
Qed.

Theorem monotone_nondec_lower_bound0 :
  forall f : set -> set,
    seq_real f ->
    monotone_nondec f ->
    is_lower_bound_seq f (f 0).
let f.
assume Hseq.
assume Hmono.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim H: forall k, nat_p k -> f 0 <= f k.
{
  apply nat_ind.
  - prove f 0 <= f 0.
    exact SNoLe_ref (f 0).
  - let k.
    assume Hk: nat_p k.
    assume IH: f 0 <= f k.
    prove f 0 <= f (ordsucc k).
    claim H0omega: 0 :e omega.
    { exact nat_p_omega 0 nat_0. }
    claim Hk_omega: k :e omega.
    { exact nat_p_omega k Hk. }
    claim Hsucc_omega: ordsucc k :e omega.
    { exact omega_ordsucc k Hk_omega. }
    claim H0in: 0 :e ordsucc k.
    { exact nat_0_in_ordsucc k Hk. }
    exact Hmono 0 H0omega (ordsucc k) Hsucc_omega H0in.
}
exact H n Hn_nat.
Qed.

Theorem monotone_noninc_upper_bound0 :
  forall f : set -> set,
    seq_real f ->
    monotone_noninc f ->
    is_upper_bound_seq f (f 0).
let f.
assume Hseq.
assume Hmono.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim H: forall k, nat_p k -> f k <= f 0.
{
  apply nat_ind.
  - prove f 0 <= f 0.
    exact SNoLe_ref (f 0).
  - let k.
    assume Hk: nat_p k.
    assume IH: f k <= f 0.
    prove f (ordsucc k) <= f 0.
    claim H0omega: 0 :e omega.
    { exact nat_p_omega 0 nat_0. }
    claim Hk_omega: k :e omega.
    { exact nat_p_omega k Hk. }
    claim Hsucc_omega: ordsucc k :e omega.
    { exact omega_ordsucc k Hk_omega. }
    claim H0in: 0 :e ordsucc k.
    { exact nat_0_in_ordsucc k Hk. }
    exact Hmono 0 H0omega (ordsucc k) Hsucc_omega H0in.
}
exact H n Hn_nat.
Qed.

Theorem bounded_below_of_monotone_nondec :
  forall f : set -> set,
    seq_real f ->
    monotone_nondec f ->
    bounded_below f.
let f.
assume Hseq.
assume Hmono.
prove exists s :e real, is_lower_bound_seq f s.
claim H0omega: 0 :e omega.
{ exact nat_p_omega 0 nat_0. }
claim Hf0: f 0 :e real.
{ exact Hseq 0 H0omega. }
witness (f 0).
apply andI (f 0 :e real) (is_lower_bound_seq f (f 0)).
- exact Hf0.
- exact monotone_nondec_lower_bound0 f Hseq Hmono.
Qed.

Theorem bounded_above_of_monotone_noninc :
  forall f : set -> set,
    seq_real f ->
    monotone_noninc f ->
    bounded_above f.
let f.
assume Hseq.
assume Hmono.
prove exists s :e real, is_upper_bound_seq f s.
claim H0omega: 0 :e omega.
{ exact nat_p_omega 0 nat_0. }
claim Hf0: f 0 :e real.
{ exact Hseq 0 H0omega. }
witness (f 0).
apply andI (f 0 :e real) (is_upper_bound_seq f (f 0)).
- exact Hf0.
- exact monotone_noninc_upper_bound0 f Hseq Hmono.
Qed.
