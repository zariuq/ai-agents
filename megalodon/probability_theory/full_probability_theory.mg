Definition partial_sum : (set -> set) -> set -> set :=
  fun f n => Sum 0 n f.

Definition is_upper_bound : (set -> set) -> set -> prop :=
  fun f s => forall n :e omega, partial_sum f n <= s.

Definition is_least_upper_bound : (set -> set) -> set -> prop :=
  fun f s =>
    is_upper_bound f s
    /\ (forall t :e real, is_upper_bound f t -> s <= t).

Definition sum_nat : (set -> set) -> set :=
  fun f => Eps_i (fun s => s :e real /\ is_least_upper_bound f s).

Definition summable : (set -> set) -> prop :=
  fun f => exists s, s :e real /\ is_least_upper_bound f s.

Definition Disjoint : set -> set -> prop :=
  fun A B => A :/\: B = Empty.

Definition pairwise_disjoint : (set -> set) -> prop :=
  fun f => forall m n :e omega, m <> n -> Disjoint (f m) (f n).

Definition bigcup_nat : (set -> set) -> set :=
  fun f => Union {f n | n :e omega}.

Definition bigcup_fin : (set -> set) -> set -> set :=
  fun f n => Union {f i | i :e n}.

Axiom real_zero_le_implies_add_le :
  forall x y, 0 <= y -> x <= x + y.

Axiom real_le_add_r :
  forall x y z, x <= y -> x + z <= y + z.

Axiom real_le_add_cancel :
  forall x y z, x + z <= y + z -> x <= y.

Axiom real_add_comm : forall x y, x + y = y + x.
Axiom real_add_assoc : forall x y z, x + (y + z) = (x + y) + z.
Axiom real_add_zero_l : forall x, 0 + x = x.
Axiom real_add_zero_r : forall x, x + 0 = x.
Axiom real_add_left_inv : forall x, x + - x = 0.

Axiom real_one_real : 1 :e real.
Axiom real_add_left_cancel :
  forall x y z, x = y + z -> x + - y = z.

Axiom real_mul_comm : forall x y, x * y = y * x.
Axiom real_mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom real_mul_one_l : forall x, 1 * x = x.
Axiom real_mul_one_r : forall x, x * 1 = x.
Axiom real_mul_zero_l : forall x, 0 * x = 0.
Axiom real_mul_zero_r : forall x, x * 0 = 0.
Axiom real_mul_add_distr : forall x y z, x * (y + z) = x * y + x * z.
Axiom real_mul_neg : forall x y, x * (- y) = - (x * y).
Axiom real_mul_div_left : forall x y :e real, y <> 0 -> y * (x :/: y) = x.
Axiom real_mul_div_cancel_right : forall x y :e real, y <> 0 -> (x * y) :/: y = x.
Axiom real_mul_real : forall x y :e real, x * y :e real.
Axiom real_pos_neq0 : forall x, 0 < x -> x <> 0.

Axiom eq_refl_set : forall x:set, x = x.
Axiom eq_sym : forall x y, x = y -> y = x.
Axiom eq_trans : forall x y z, x = y -> y = z -> x = z.
Axiom func_congr : forall f : set -> set, forall x y : set, x = y -> f x = f y.

Theorem real_leq_antisym :
  forall x y :e real, x <= y -> y <= x -> x = y.
let x.
assume Hx: x :e real.
let y.
assume Hy: y :e real.
assume Hxy. assume Hyx.
claim HxS: SNo x. { exact real_SNo x Hx. }
claim HyS: SNo y. { exact real_SNo y Hy. }
exact SNoLe_antisym x y HxS HyS Hxy Hyx.
Qed.

Theorem least_upper_bound_unique :
  forall f : set -> set,
  forall s t :e real,
    is_least_upper_bound f s ->
    is_least_upper_bound f t ->
    s = t.
let f.
let s.
assume Hs: s :e real.
let t.
assume Ht: t :e real.
assume Hs_lub: is_least_upper_bound f s.
assume Ht_lub: is_least_upper_bound f t.
claim Hs_upper: is_upper_bound f s.
  exact andEL (is_upper_bound f s)
              (forall t0 :e real, is_upper_bound f t0 -> s <= t0)
              Hs_lub.
claim Hs_min: forall t0 :e real, is_upper_bound f t0 -> s <= t0.
  exact andER (is_upper_bound f s)
              (forall t0 :e real, is_upper_bound f t0 -> s <= t0)
              Hs_lub.
claim Ht_upper: is_upper_bound f t.
  exact andEL (is_upper_bound f t)
              (forall t0 :e real, is_upper_bound f t0 -> t <= t0)
              Ht_lub.
claim Ht_min: forall t0 :e real, is_upper_bound f t0 -> t <= t0.
  exact andER (is_upper_bound f t)
              (forall t0 :e real, is_upper_bound f t0 -> t <= t0)
              Ht_lub.
claim Hst: s <= t.
  exact Hs_min t Ht Ht_upper.
claim Hts: t <= s.
  exact Ht_min s Hs Hs_upper.
exact real_leq_antisym s Hs t Ht Hst Hts.
Qed.

Theorem summable_unique_lub :
  forall f : set -> set, summable f ->
  forall s t :e real,
    is_least_upper_bound f s ->
    is_least_upper_bound f t ->
    s = t.
let f.
assume Hsummable.
let s.
assume Hs: s :e real.
let t.
assume Ht: t :e real.
assume Hs_lub: is_least_upper_bound f s.
assume Ht_lub: is_least_upper_bound f t.
exact least_upper_bound_unique f s Hs t Ht Hs_lub Ht_lub.
Qed.

Theorem sum_nat_spec :
  forall f : set -> set,
    summable f ->
    sum_nat f :e real /\ is_least_upper_bound f (sum_nat f).
let f.
assume Hsummable.
exact Eps_i_ex (fun s => s :e real /\ is_least_upper_bound f s) Hsummable.
Qed.

Theorem sum_nat_real :
  forall f : set -> set,
    summable f ->
    sum_nat f :e real.
let f.
assume Hsummable.
exact andEL (sum_nat f :e real)
            (is_least_upper_bound f (sum_nat f))
            (sum_nat_spec f Hsummable).
Qed.

Theorem sum_nat_is_least_upper_bound :
  forall f : set -> set,
    summable f ->
    is_least_upper_bound f (sum_nat f).
let f.
assume Hsummable.
exact andER (sum_nat f :e real)
            (is_least_upper_bound f (sum_nat f))
            (sum_nat_spec f Hsummable).
Qed.

Theorem partial_sum_zero :
  forall n :e omega, partial_sum (fun n => 0) n = 0.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim Hgen: forall k, nat_p k -> partial_sum (fun n => 0) k = 0.
{
  apply nat_ind.
  - prove partial_sum (fun n => 0) 0 = 0.
    claim Hdef: partial_sum (fun n => 0) 0 =
      nat_primrec 0 (fun k r => if k :e 0 then 0 else 0 + r) (ordsucc 0).
    { reflexivity. }
    rewrite Hdef.
    rewrite (nat_primrec_S 0 (fun k r => if k :e 0 then 0 else 0 + r) 0 nat_0).
    rewrite (nat_primrec_0 0 (fun k r => if k :e 0 then 0 else 0 + r)).
    rewrite (If_i_0 (0 :e 0) 0 (0 + 0) nIn_0_0).
    rewrite (real_add_zero_l 0).
    reflexivity.
  - let k.
    assume Hk: nat_p k.
    assume IH: partial_sum (fun n => 0) k = 0.
    prove partial_sum (fun n => 0) (ordsucc k) = 0.
    claim Hdef: partial_sum (fun n => 0) (ordsucc k) =
      nat_primrec 0 (fun i r => if i :e 0 then 0 else 0 + r) (ordsucc (ordsucc k)).
    { reflexivity. }
    rewrite Hdef.
    rewrite (nat_primrec_S 0 (fun i r => if i :e 0 then 0 else 0 + r) (ordsucc k) (nat_ordsucc k Hk)).
    claim Hdefk: nat_primrec 0 (fun i r => if i :e 0 then 0 else 0 + r) (ordsucc k)
      = partial_sum (fun n => 0) k.
    { reflexivity. }
    rewrite Hdefk.
    rewrite IH.
    rewrite (If_i_0 (ordsucc k :e 0) 0 (0 + 0) (EmptyE (ordsucc k))).
    rewrite (real_add_zero_l 0).
    reflexivity.
}
exact Hgen n Hn_nat.
Qed.

Theorem partial_sum_pair_zero :
  forall a b :e real,
    partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) 0 = a.
let a.
assume Ha: a :e real.
let b.
assume Hb: b :e real.
claim Hdef: partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) 0 =
  nat_primrec 0
    (fun k r => if k :e 0 then 0 else (If_i (k = 0) a (If_i (k = 1) b 0)) + r)
    (ordsucc 0).
{ reflexivity. }
rewrite Hdef.
rewrite (nat_primrec_S 0 (fun k r => if k :e 0 then 0 else (If_i (k = 0) a (If_i (k = 1) b 0)) + r) 0 nat_0).
rewrite (nat_primrec_0 0 (fun k r => if k :e 0 then 0 else (If_i (k = 0) a (If_i (k = 1) b 0)) + r)).
rewrite (If_i_0 (0 :e 0) 0 ((If_i (0 = 0) a (If_i (0 = 1) b 0)) + 0) nIn_0_0).
claim H00: 0 = 0. { reflexivity. }
rewrite (If_i_1 (0 = 0) a (If_i (0 = 1) b 0) H00).
rewrite (real_add_zero_r a).
reflexivity.
Qed.

Theorem partial_sum_pair_succ :
  forall a b :e real,
    forall n :e omega,
      partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc n) = a + b.
let a.
assume Ha: a :e real.
let b.
assume Hb: b :e real.
let n.
assume Hn: n :e omega.
claim Hn_nat: nat_p n.
{ exact omega_nat_p n Hn. }
claim Hgen: forall k, nat_p k -> partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc k) = a + b.
{
  apply nat_ind.
  - prove partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc 0) = a + b.
    claim Hdef: partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc 0) =
      nat_primrec 0
        (fun k r => if k :e 0 then 0 else (If_i (k = 0) a (If_i (k = 1) b 0)) + r)
        (ordsucc (ordsucc 0)).
    { reflexivity. }
    rewrite Hdef.
    rewrite (nat_primrec_S 0 (fun k r => if k :e 0 then 0 else (If_i (k = 0) a (If_i (k = 1) b 0)) + r) 1 nat_1).
    rewrite (nat_primrec_S 0 (fun k r => if k :e 0 then 0 else (If_i (k = 0) a (If_i (k = 1) b 0)) + r) 0 nat_0).
    rewrite (nat_primrec_0 0 (fun k r => if k :e 0 then 0 else (If_i (k = 0) a (If_i (k = 1) b 0)) + r)).
    rewrite (If_i_0 (0 :e 0) 0 ((If_i (0 = 0) a (If_i (0 = 1) b 0)) + 0) nIn_0_0).
    claim H00: 0 = 0. { reflexivity. }
    rewrite (If_i_1 (0 = 0) a (If_i (0 = 1) b 0) H00).
    rewrite (real_add_zero_r a).
    rewrite (If_i_0 (1 :e 0) 0 ((If_i (1 = 0) a (If_i (1 = 1) b 0)) + a) nIn_1_0).
    rewrite (If_i_0 (1 = 0) a (If_i (1 = 1) b 0) neq_1_0).
    claim H11: 1 = 1. { reflexivity. }
    rewrite (If_i_1 (1 = 1) b 0 H11).
    rewrite (real_add_comm b a).
    reflexivity.
  - let k.
    assume Hk: nat_p k.
    assume IH: partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc k) = a + b.
    prove partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc (ordsucc k)) = a + b.
    claim Hdef: partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc (ordsucc k)) =
      nat_primrec 0
        (fun i r => if i :e 0 then 0 else (If_i (i = 0) a (If_i (i = 1) b 0)) + r)
        (ordsucc (ordsucc (ordsucc k))).
    { reflexivity. }
    rewrite Hdef.
    rewrite (nat_primrec_S 0 (fun i r => if i :e 0 then 0 else (If_i (i = 0) a (If_i (i = 1) b 0)) + r) (ordsucc (ordsucc k)) (nat_ordsucc (ordsucc k) (nat_ordsucc k Hk))).
    claim Hdefk: nat_primrec 0
      (fun i r => if i :e 0 then 0 else (If_i (i = 0) a (If_i (i = 1) b 0)) + r)
      (ordsucc (ordsucc k))
      = partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc k).
    { reflexivity. }
    rewrite Hdefk.
    rewrite IH.
    rewrite (If_i_0 (ordsucc (ordsucc k) :e 0) 0 ((If_i (ordsucc (ordsucc k) = 0) a (If_i (ordsucc (ordsucc k) = 1) b 0)) + (a + b)) (EmptyE (ordsucc (ordsucc k)))).
    claim Hneq0: ordsucc (ordsucc k) <> 0.
    { exact neq_ordsucc_0 (ordsucc k). }
    claim Hneq1: ordsucc (ordsucc k) <> 1.
    {
      claim Hneq: ordsucc k <> 0.
      { exact neq_ordsucc_0 k. }
      exact ordsucc_inj_contra (ordsucc k) 0 Hneq.
    }
    rewrite (If_i_0 (ordsucc (ordsucc k) = 0) a (If_i (ordsucc (ordsucc k) = 1) b 0) Hneq0).
    rewrite (If_i_0 (ordsucc (ordsucc k) = 1) b 0 Hneq1).
    rewrite (real_add_zero_l (a + b)).
    reflexivity.
}
exact Hgen n Hn_nat.
Qed.

Theorem pair_is_least_upper_bound :
  forall a b :e real,
    0 <= b ->
    is_least_upper_bound
      (fun n => If_i (n = 0) a (If_i (n = 1) b 0))
      (a + b).
let a.
assume Ha: a :e real.
let b.
assume Hb: b :e real.
assume Hb_nonneg.
apply andI (is_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (a + b))
           (forall t :e real, is_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) t -> a + b <= t).
- prove is_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (a + b).
  let n.
  assume Hn: n :e omega.
  claim Hn_nat: nat_p n.
  { exact omega_nat_p n Hn. }
  apply (nat_inv n Hn_nat).
  * assume Hn0: n = 0.
    rewrite Hn0.
    rewrite (partial_sum_pair_zero a Ha b Hb).
    exact real_zero_le_implies_add_le a b Hb_nonneg.
  * assume Hn_succ: exists k, nat_p k /\ n = ordsucc k.
    apply (exandE_i nat_p (fun k => n = ordsucc k) Hn_succ).
    let k.
    assume Hk_nat: nat_p k.
    assume Hn_eq: n = ordsucc k.
    rewrite Hn_eq.
    claim Hk_omega: k :e omega.
    { exact nat_p_omega k Hk_nat. }
    rewrite (partial_sum_pair_succ a Ha b Hb k Hk_omega).
    exact SNoLe_ref (a + b).
- prove forall t :e real, is_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) t -> a + b <= t.
  let t.
  assume Ht_real: t :e real.
  assume Ht_upper: is_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) t.
  claim H0_omega: 0 :e omega.
  { exact nat_p_omega 0 nat_0. }
  claim H1_omega: ordsucc 0 :e omega.
  { exact omega_ordsucc 0 H0_omega. }
  claim Hps1: partial_sum (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (ordsucc 0) <= t.
  { exact Ht_upper (ordsucc 0) H1_omega. }
  claim Hps1': a + b <= t.
  {
    rewrite <- (partial_sum_pair_succ a Ha b Hb 0 H0_omega).
    exact Hps1.
  }
  exact Hps1'.
Qed.

Theorem sum_nat_zero : sum_nat (fun n => 0) = 0.
claim Hub: is_upper_bound (fun n => 0) 0.
{
  let n.
  assume Hn: n :e omega.
  rewrite (partial_sum_zero n Hn).
  exact SNoLe_ref 0.
}
claim Hlub: is_least_upper_bound (fun n => 0) 0.
{
  apply andI (is_upper_bound (fun n => 0) 0) (forall t :e real, is_upper_bound (fun n => 0) t -> 0 <= t).
  - exact Hub.
  - let t.
    assume Ht_real: t :e real.
    assume Ht_upper: is_upper_bound (fun n => 0) t.
    claim H0_omega: 0 :e omega.
    { exact nat_p_omega 0 nat_0. }
    claim Hps0: partial_sum (fun n => 0) 0 <= t.
    { exact Ht_upper 0 H0_omega. }
    claim Hps0': 0 <= t.
    {
      rewrite <- (partial_sum_zero 0 H0_omega).
      exact Hps0.
    }
    exact Hps0'.
}
claim Hsum_wit: 0 :e real /\ is_least_upper_bound (fun n => 0) 0.
{
  apply andI (0 :e real) (is_least_upper_bound (fun n => 0) 0).
  - exact real_0.
  - exact Hlub.
}
claim Hsum_nat: sum_nat (fun n => 0) :e real /\ is_least_upper_bound (fun n => 0) (sum_nat (fun n => 0)).
{
  exact Eps_i_ax (fun s => s :e real /\ is_least_upper_bound (fun n => 0) s) 0 Hsum_wit.
}
claim Hsum_real: sum_nat (fun n => 0) :e real.
{ exact andEL (sum_nat (fun n => 0) :e real) (is_least_upper_bound (fun n => 0) (sum_nat (fun n => 0))) Hsum_nat. }
claim Hsum_lub: is_least_upper_bound (fun n => 0) (sum_nat (fun n => 0)).
{ exact andER (sum_nat (fun n => 0) :e real) (is_least_upper_bound (fun n => 0) (sum_nat (fun n => 0))) Hsum_nat. }
exact least_upper_bound_unique (fun n => 0) (sum_nat (fun n => 0)) Hsum_real 0 real_0 Hsum_lub Hlub.
Qed.

Theorem sum_nat_pair :
  forall a b :e real,
    0 <= b ->
    sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) = a + b.
let a.
assume Ha: a :e real.
let b.
assume Hb: b :e real.
assume Hb_nonneg.
claim HaS: SNo a. { exact real_SNo a Ha. }
claim HbS: SNo b. { exact real_SNo b Hb. }
claim Hab_sno: add_SNo a b :e real.
{ exact real_add_SNo a Ha b Hb. }
claim Hab_eq: add_SNo a b = a + b.
{ exact add_SNo_add_CSNo a b HaS HbS. }
claim Hab_real: a + b :e real.
{
  rewrite <- Hab_eq.
  exact Hab_sno.
}
claim Hlub: is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (a + b).
{ exact pair_is_least_upper_bound a Ha b Hb Hb_nonneg. }
claim Hsum_wit: a + b :e real /\ is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (a + b).
{
  apply andI (a + b :e real) (is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (a + b)).
  - exact Hab_real.
  - exact Hlub.
}
claim Hsum_nat: sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) :e real /\ is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0))).
{
  exact Eps_i_ax (fun s => s :e real /\ is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) s) (a + b) Hsum_wit.
}
claim Hsum_real: sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) :e real.
{ exact andEL (sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) :e real) (is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)))) Hsum_nat. }
claim Hsum_lub: is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0))).
{ exact andER (sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) :e real) (is_least_upper_bound (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)))) Hsum_nat. }
exact least_upper_bound_unique (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) (sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0))) Hsum_real (a + b) Hab_real Hsum_lub Hlub.
Qed.



Definition is_field : set -> set -> prop :=
  fun Omega F =>
    (forall A :e F, A c= Omega)
    /\ Omega :e F
    /\ Empty :e F
    /\ (forall A :e F, (Omega :\: A) :e F)
    /\ (forall A B, A :e F -> B :e F -> (A :\/: B) :e F).

Theorem field_has_omega :
  forall Omega F, is_field Omega F -> Omega :e F.
let Omega. let F.
assume H: is_field Omega F.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              H.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
exact andER (forall A :e F, A c= Omega)
            (Omega :e F)
            H12.
Qed.

Theorem field_complement_closed :
  forall Omega F A,
    is_field Omega F ->
    A :e F ->
    (Omega :\: A) :e F.
let Omega. let F. let A.
assume HF. assume HA.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim Hcompl: forall A :e F, (Omega :\: A) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
exact Hcompl A HA.
Qed.

Theorem field_subset :
  forall Omega F A,
    is_field Omega F ->
    A :e F ->
    A c= Omega.
let Omega. let F. let A.
assume HF. assume HA.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
claim Hsub: forall A :e F, A c= Omega.
  exact andEL (forall A :e F, A c= Omega) (Omega :e F) H12.
exact Hsub A HA.
Qed.

Theorem field_closed_under_intersection :
  forall Omega F A B,
    is_field Omega F ->
    A :e F -> B :e F ->
    (A :/\: B) :e F.
let Omega. let F. let A. let B.
assume HF: is_field Omega F.
assume HA: A :e F.
assume HB: B :e F.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
claim H_union: forall A B, A :e F -> B :e F -> (A :\/: B) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim H_compl: forall A :e F, (Omega :\: A) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H_sub: forall A :e F, A c= Omega.
  exact andEL (forall A :e F, A c= Omega)
              (Omega :e F)
              H12.
claim HA_sub: A c= Omega. exact H_sub A HA.
claim HB_sub: B c= Omega. exact H_sub B HB.
claim HAc: (Omega :\: A) :e F. exact H_compl A HA.
claim HBc: (Omega :\: B) :e F. exact H_compl B HB.
claim HU: (Omega :\: A) :\/: (Omega :\: B) :e F.
  exact H_union (Omega :\: A) (Omega :\: B) HAc HBc.
claim HRes: (Omega :\: ((Omega :\: A) :\/: (Omega :\: B))) :e F.
  exact H_compl ((Omega :\: A) :\/: (Omega :\: B)) HU.
claim Heq: A :/\: B = Omega :\: ((Omega :\: A) :\/: (Omega :\: B)).
{ apply set_ext.
  - prove A :/\: B c= Omega :\: ((Omega :\: A) :\/: (Omega :\: B)).
    let z.
    assume Hz: z :e A :/\: B.
    apply setminusI.
    + exact H_sub A HA z (binintersectE1 A B z Hz).
    + assume HContra.
      apply orE (z :e Omega :\: A) (z :e Omega :\: B) False (fun H => setminusE2 Omega A z H (binintersectE1 A B z Hz)) (fun H => setminusE2 Omega B z H (binintersectE2 A B z Hz)) (binunionE (Omega :\: A) (Omega :\: B) z HContra).
  - prove (Omega :\: ((Omega :\: A) :\/: (Omega :\: B))) c= A :/\: B.
    let z.
    assume Hz: z :e Omega :\: ((Omega :\: A) :\/: (Omega :\: B)).
    apply binintersectI.
    + claim zInOmega: z :e Omega. exact setminusE1 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim zNotUnion: z /:e (Omega :\: A) :\/: (Omega :\: B). exact setminusE2 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim HNotUnionSplit: z /:e (Omega :\: A) /\ z /:e (Omega :\: B). exact binunion_nIn_E (Omega :\: A) (Omega :\: B) z zNotUnion.
      claim HNotDiffA: z /:e (Omega :\: A). exact andEL (z /:e (Omega :\: A)) (z /:e (Omega :\: B)) HNotUnionSplit.
      apply orE (z :e A) (z /:e A) (z :e A) (fun H => H) (fun HnA => FalseE (HNotDiffA (setminusI Omega A z zInOmega HnA)) (z :e A)) (xm (z :e A)).
    + claim zInOmega: z :e Omega. exact setminusE1 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim zNotUnion: z /:e (Omega :\: A) :\/: (Omega :\: B). exact setminusE2 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim HNotUnionSplit: z /:e (Omega :\: A) /\ z /:e (Omega :\: B). exact binunion_nIn_E (Omega :\: A) (Omega :\: B) z zNotUnion.
      claim HNotDiffB: z /:e (Omega :\: B). exact andER (z /:e (Omega :\: A)) (z /:e (Omega :\: B)) HNotUnionSplit.
      apply orE (z :e B) (z /:e B) (z :e B) (fun H => H) (fun HnB => FalseE (HNotDiffB (setminusI Omega B z zInOmega HnB)) (z :e B)) (xm (z :e B)).
}
exact Heq (fun _ X => X :e F) HRes.
Qed.

Definition is_sigma_field : set -> set -> prop :=
  fun Omega F =>
    is_field Omega F
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         bigcup_nat f :e F).

Theorem sigma_field_is_field :
  forall Omega F,
    is_sigma_field Omega F ->
    is_field Omega F.
let Omega. let F.
assume H: is_sigma_field Omega F.
exact andEL (is_field Omega F) (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F) H.
Qed.

Definition is_probability_measure : set -> set -> (set -> set) -> prop :=
  fun Omega F P =>
    is_sigma_field Omega F
    /\ ((forall A :e F, P A :e real /\ 0 <= P A)
    /\ (P Omega = 1
    /\ (P Empty = 0
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         pairwise_disjoint f ->
         P (bigcup_nat f) = sum_nat (fun n => P (f n)))))).

Theorem prob_value_real :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    forall A :e F, P A :e real.
let Omega. let F. let P.
assume H.
claim H_rest: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
claim H_val: forall A :e F, P A :e real /\ 0 <= P A.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A)
              (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) H_rest.
let A.
assume HA: A :e F.
exact andEL (P A :e real) (0 <= P A) (H_val A HA).
Qed.

Theorem prob_measure_is_sigma_field :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    is_sigma_field Omega F.
let Omega. let F. let P.
assume H.
exact andEL (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
Qed.

Theorem prob_empty_zero :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    P Empty = 0.
let Omega. let F. let P.
assume H: is_probability_measure Omega F P.
claim H_rest: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
claim H_rest2: P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))).
  exact andER (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) H_rest.
claim H_rest3: P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  exact andER (P Omega = 1) (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H_rest2.
exact andEL (P Empty = 0) (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))) H_rest3.
Qed.

Theorem prob_finite_additivity :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    Disjoint A B ->
    P (A :\/: B) = P A + P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hd.
claim HF: is_field Omega F.
{
  exact sigma_field_is_field Omega F (prob_measure_is_sigma_field Omega F P H).
}
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim FEmpty: Empty :e F.
  exact andER ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.

set f := fun n : set => If_i (n = 0) A (If_i (n = 1) B Empty).

claim Ff: forall n :e omega, f n :e F.
{
  let n. assume Hn.
  claim Eq: f n = If_i (n=0) A (If_i (n=1) B Empty). { reflexivity. }
  claim C0: n = 0 -> f n :e F.
  {
    assume Hz.
    rewrite Eq.
    rewrite (If_i_1 (n=0) A (If_i (n=1) B Empty) Hz).
    exact HA.
  }
  claim Cnot0: n <> 0 -> f n :e F.
  {
    assume Hnz.
    rewrite Eq.
    rewrite (If_i_0 (n=0) A (If_i (n=1) B Empty) Hnz).
    claim C1: n = 1 -> If_i (n=1) B Empty :e F.
    {
      assume H1.
      rewrite (If_i_1 (n=1) B Empty H1).
      exact HB.
    }
    claim Cnot1: n <> 1 -> If_i (n=1) B Empty :e F.
    {
      assume Hn1.
      rewrite (If_i_0 (n=1) B Empty Hn1).
      exact FEmpty.
    }
    exact orE (n=1) (n<>1) (If_i (n=1) B Empty :e F) C1 Cnot1 (xm (n=1)).
  }
  exact orE (n=0) (n<>0) (f n :e F) C0 Cnot0 (xm (n=0)).
}

claim Fdisj: pairwise_disjoint f.
{
  let m. assume Hm_in. let n. assume Hn_in. assume Hmn.
  apply orE (m = 0) (m <> 0) (Disjoint (f m) (f n)).
  - assume Hm0.
    apply orE (n = 1) (n <> 1) (Disjoint (f m) (f n)).
    + assume Hn1.
      rewrite Hm0. rewrite Hn1.
      claim Hf0: f 0 = A.
      {
        claim Eq0: f 0 = If_i (0=0) A (If_i (0=1) B Empty). { reflexivity. }
        rewrite Eq0.
        claim H00: 0 = 0. { reflexivity. }
        rewrite (If_i_1 (0=0) A (If_i (0=1) B Empty) H00).
        reflexivity.
      }
      claim Hf1: f 1 = B.
      {
        claim Eq1: f 1 = If_i (1=0) A (If_i (1=1) B Empty). { reflexivity. }
        rewrite Eq1.
        claim H11: 1 = 1. { reflexivity. }
        rewrite (If_i_0 (1=0) A (If_i (1=1) B Empty) neq_1_0).
        rewrite (If_i_1 (1=1) B Empty H11).
        reflexivity.
      }
      rewrite Hf0. rewrite Hf1.
      exact Hd.
    + assume Hn1.
      claim Hn0: n <> 0.
      {
        assume Hn0eq.
        apply Hmn.
        rewrite Hm0. rewrite Hn0eq.
        reflexivity.
      }
      rewrite Hm0.
      claim Hf0: f 0 = A.
      {
        claim Eq0: f 0 = If_i (0=0) A (If_i (0=1) B Empty). { reflexivity. }
        rewrite Eq0.
        claim H00: 0 = 0. { reflexivity. }
        rewrite (If_i_1 (0=0) A (If_i (0=1) B Empty) H00).
        reflexivity.
      }
      claim Hfn: f n = Empty.
      {
        claim Eqn: f n = If_i (n=0) A (If_i (n=1) B Empty). { reflexivity. }
        rewrite Eqn.
        rewrite (If_i_0 (n=0) A (If_i (n=1) B Empty) Hn0).
        rewrite (If_i_0 (n=1) B Empty Hn1).
        reflexivity.
      }
      rewrite Hf0. rewrite Hfn.
      claim Hsub: A :/\: Empty c= Empty.
      {
        let z. assume Hz.
        exact EmptyE z (binintersectE2 A Empty z Hz) (z :e Empty).
      }
      exact Empty_Subq_eq (A :/\: Empty) Hsub.
    + exact xm (n = 1).
  - assume Hm0.
    apply orE (m = 1) (m <> 1) (Disjoint (f m) (f n)).
    + assume Hm1.
      apply orE (n = 0) (n <> 0) (Disjoint (f m) (f n)).
      * assume Hn0.
        rewrite Hm1. rewrite Hn0.
        claim Hf1: f 1 = B.
        {
          claim Eq1: f 1 = If_i (1=0) A (If_i (1=1) B Empty). { reflexivity. }
          rewrite Eq1.
          claim H11: 1 = 1. { reflexivity. }
          rewrite (If_i_0 (1=0) A (If_i (1=1) B Empty) neq_1_0).
          rewrite (If_i_1 (1=1) B Empty H11).
          reflexivity.
        }
        claim Hf0: f 0 = A.
        {
          claim Eq0: f 0 = If_i (0=0) A (If_i (0=1) B Empty). { reflexivity. }
          rewrite Eq0.
          claim H00: 0 = 0. { reflexivity. }
          rewrite (If_i_1 (0=0) A (If_i (0=1) B Empty) H00).
          reflexivity.
        }
        rewrite Hf1. rewrite Hf0.
        claim HdSym: B :/\: A = Empty.
        { rewrite (binintersect_com B A). exact Hd. }
        exact HdSym.
      * assume Hn0.
        claim Hn1: n <> 1.
        {
          assume Hn1eq.
          apply Hmn.
          rewrite Hm1. rewrite Hn1eq.
          reflexivity.
        }
        claim Hf1: f 1 = B.
        {
          claim Eq1: f 1 = If_i (1=0) A (If_i (1=1) B Empty). { reflexivity. }
          rewrite Eq1.
          claim H11: 1 = 1. { reflexivity. }
          rewrite (If_i_0 (1=0) A (If_i (1=1) B Empty) neq_1_0).
          rewrite (If_i_1 (1=1) B Empty H11).
          reflexivity.
        }
        claim Hfn: f n = Empty.
        {
          claim Eqn: f n = If_i (n=0) A (If_i (n=1) B Empty). { reflexivity. }
          rewrite Eqn.
          rewrite (If_i_0 (n=0) A (If_i (n=1) B Empty) Hn0).
          rewrite (If_i_0 (n=1) B Empty Hn1).
          reflexivity.
        }
        rewrite Hm1. rewrite Hf1. rewrite Hfn.
        claim Hsub: B :/\: Empty c= Empty.
        {
          let z. assume Hz.
          exact EmptyE z (binintersectE2 B Empty z Hz) (z :e Empty).
        }
        exact Empty_Subq_eq (B :/\: Empty) Hsub.
      * exact xm (n = 0).
    + assume Hm1.
      claim HfmEmpty: f m = Empty.
      {
        claim Eqm: f m = If_i (m=0) A (If_i (m=1) B Empty). { reflexivity. }
        rewrite Eqm.
        rewrite (If_i_0 (m=0) A (If_i (m=1) B Empty) Hm0).
        rewrite (If_i_0 (m=1) B Empty Hm1).
        reflexivity.
      }
      rewrite HfmEmpty.
      claim Hsub: Empty :/\: (f n) c= Empty.
      {
        exact binintersect_Subq_1 Empty (f n).
      }
      exact Empty_Subq_eq (Empty :/\: (f n)) Hsub.
    + exact xm (m = 1).
  - exact xm (m = 0).
}



claim HUnionSym: A :\/: B = bigcup_nat f.
{
  claim BigDef: bigcup_nat f = Union {f n|n :e omega}. { reflexivity. }
  apply set_ext.
  - prove A :\/: B c= bigcup_nat f.
    let z. assume HzUnion.
    apply binunionE A B z HzUnion.
    + assume HzA: z :e A.
      claim H0in: 0 :e omega. { exact nat_p_omega 0 nat_0. }
      claim Hfam0: f 0 :e {f n|n :e omega}. { exact ReplI omega f 0 H0in. }
      claim HzIn0: z :e f 0.
      {
        claim Eqf0: f 0 = If_i (0=0) A (If_i (0=1) B Empty). { reflexivity. }
        rewrite Eqf0.
        claim H00: 0 = 0. { reflexivity. }
        rewrite (If_i_1 (0=0) A (If_i (0=1) B Empty) H00).
        exact HzA.
      }
      rewrite BigDef.
      exact UnionI {f n|n :e omega} z (f 0) HzIn0 Hfam0.
    + assume HzB: z :e B.
      claim H1in: 1 :e omega. { exact nat_p_omega 1 nat_1. }
      claim Hfam1: f 1 :e {f n|n :e omega}. { exact ReplI omega f 1 H1in. }
      claim HzIn1: z :e f 1.
      {
        claim Eqf1: f 1 = If_i (1=0) A (If_i (1=1) B Empty). { reflexivity. }
        rewrite Eqf1.
        rewrite (If_i_0 (1=0) A (If_i (1=1) B Empty) neq_1_0).
        claim H11: 1 = 1. { reflexivity. }
        rewrite (If_i_1 (1=1) B Empty H11).
        exact HzB.
      }
      rewrite BigDef.
      exact UnionI {f n|n :e omega} z (f 1) HzIn1 Hfam1.
  - prove bigcup_nat f c= A :\/: B.
    let z. assume Hz.
    claim Hz': z :e Union {f n|n :e omega}.
    { rewrite <- BigDef. exact Hz. }
    apply UnionE_impred {f n|n :e omega} z Hz'.
    let Y. assume HzInY HYIn.
    apply ReplE_impred omega f Y HYIn.
    let n. assume Hn HYeq.
    claim HzIn_fn: z :e f n.
    { claim Heq: f n = Y. { symmetry. exact HYeq. }
      rewrite Heq. exact HzInY. }
    apply orE (n = 0) (n <> 0) (z :e A :\/: B).
    + assume H0.
      claim HzInA: z :e A.
      { rewrite <- (If_i_1 (n=0) A (If_i (n=1) B Empty) H0). exact HzIn_fn. }
      exact binunionI1 A B z HzInA.
    + assume Hn0.
      claim HzIn_fn': z :e If_i (n=1) B Empty.
      { rewrite <- (If_i_0 (n=0) A (If_i (n=1) B Empty) Hn0). exact HzIn_fn. }
    apply orE (n = 1) (n <> 1) (z :e A :\/: B).
    - assume H1.
      claim HzInB: z :e B.
      { rewrite <- (If_i_1 (n=1) B Empty H1). exact HzIn_fn'. }
      exact binunionI2 A B z HzInB.
    - assume Hn1.
      claim HzEmpty: z :e Empty.
      { rewrite <- (If_i_0 (n=1) B Empty Hn1). exact HzIn_fn'. }
      apply FalseE ((EmptyE z) HzEmpty) (z :e A :\/: B).
    - exact xm (n = 1).
    + exact xm (n = 0).
}

claim HSum: P (bigcup_nat f) = sum_nat (fun n => P (f n)).
{
  claim H1: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  { exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H. }
  claim H2: P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))).
  { exact andER (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) H1. }
  claim H3: P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  { exact andER (P Omega = 1) (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H2. }
  claim Hadd: forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)).
  { exact andER (P Empty = 0) (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))) H3. }
  exact Hadd f Ff Fdisj.
}

claim HSumVal: sum_nat (fun n => P (f n)) = P A + P B.
{
  claim Hrest: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  { exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H. }
  claim Hnonneg: forall A :e F, P A :e real /\ 0 <= P A.
  { exact andEL (forall A :e F, P A :e real /\ 0 <= P A)
                (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))
                Hrest. }
  claim HPA_real: P A :e real.
  { exact andEL (P A :e real) (0 <= P A) (Hnonneg A HA). }
  claim HPB_real: P B :e real.
  { exact andEL (P B :e real) (0 <= P B) (Hnonneg B HB). }
  claim HPB_nonneg: 0 <= P B.
  { exact andER (P B :e real) (0 <= P B) (Hnonneg B HB). }
  claim HEmpty0: P Empty = 0.
  {
    claim Hrest2: P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))).
    { exact andER (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) Hrest. }
    exact andEL (P Empty = 0) (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))) (andER (P Omega = 1) (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) Hrest2).
  }
  claim Hfun_eq: (fun n:set => P (f n)) = (fun n:set => If_i (n = 0) (P A) (If_i (n = 1) (P B) 0)).
  {
    apply func_ext set set.
    let n.
    apply orE (n = 0) (n <> 0) (P (f n) = If_i (n = 0) (P A) (If_i (n = 1) (P B) 0)).
    - assume Hn0.
      rewrite Hn0.
      claim Eq0: f 0 = If_i (0=0) A (If_i (0=1) B Empty). { reflexivity. }
      rewrite Eq0.
      claim H00: 0 = 0. { reflexivity. }
      rewrite (If_i_1 (0=0) A (If_i (0=1) B Empty) H00).
      rewrite (If_i_1 (0=0) (P A) (If_i (0=1) (P B) 0) H00).
      reflexivity.
    - assume Hn0.
      apply orE (n = 1) (n <> 1) (P (f n) = If_i (n = 0) (P A) (If_i (n = 1) (P B) 0)).
      + assume Hn1.
        rewrite Hn1.
        claim Eq1: f 1 = If_i (1=0) A (If_i (1=1) B Empty). { reflexivity. }
        rewrite Eq1.
        claim H11: 1 = 1. { reflexivity. }
        rewrite (If_i_0 (1=0) A (If_i (1=1) B Empty) neq_1_0).
        rewrite (If_i_1 (1=1) B Empty H11).
        rewrite (If_i_0 (1=0) (P A) (If_i (1=1) (P B) 0) neq_1_0).
        rewrite (If_i_1 (1=1) (P B) 0 H11).
        reflexivity.
      + assume Hn1.
        claim HfnEmpty: f n = Empty.
        {
          claim Eqn: f n = If_i (n=0) A (If_i (n=1) B Empty). { reflexivity. }
          rewrite Eqn.
          rewrite (If_i_0 (n=0) A (If_i (n=1) B Empty) Hn0).
          rewrite (If_i_0 (n=1) B Empty Hn1).
          reflexivity.
        }
        rewrite HfnEmpty.
        rewrite HEmpty0.
        rewrite (If_i_0 (n=0) (P A) (If_i (n=1) (P B) 0) Hn0).
        rewrite (If_i_0 (n=1) (P B) 0 Hn1).
        reflexivity.
      + exact xm (n = 1).
    - exact xm (n = 0).
  }
  rewrite Hfun_eq.
  apply sum_nat_pair.
  - exact HPA_real.
  - exact HPB_real.
  - exact HPB_nonneg.
}

rewrite HUnionSym.
rewrite HSum.
rewrite HSumVal.
reflexivity.
Qed.

Theorem prob_monotone :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    A c= B ->
    P A <= P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hab.
claim Hsigma: is_sigma_field Omega F.
  exact prob_measure_is_sigma_field Omega F P H.
claim Hfield: is_field Omega F.
  exact sigma_field_is_field Omega F Hsigma.
claim Hrest: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
claim Hnonneg: forall X :e F, P X :e real /\ 0 <= P X.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) Hrest.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              Hfield.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
claim Hcompl: forall X :e F, (Omega :\: X) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim Hsub: forall X :e F, X c= Omega.
  exact andEL (forall A :e F, A c= Omega) (Omega :e F) H12.
claim HBAeq: (B :\: A) = B :/\: (Omega :\: A).
{
  apply set_ext.
  - prove B :\: A c= B :/\: (Omega :\: A).
    let z. assume Hz.
    apply binintersectI.
    + exact setminusE1 B A z Hz.
    + claim HzOmega: z :e Omega. exact Hsub B HB z (setminusE1 B A z Hz).
      exact setminusI Omega A z HzOmega (setminusE2 B A z Hz).
  - prove B :/\: (Omega :\: A) c= B :\: A.
    let z. assume Hz.
    claim HzB: z :e B. exact binintersectE1 B (Omega :\: A) z Hz.
    claim HzNotA: z /:e A. exact setminusE2 Omega A z (binintersectE2 B (Omega :\: A) z Hz).
    exact setminusI B A z HzB HzNotA.
}
claim HBA_in: (B :\: A) :e F.
{
  claim HBcomplA: (Omega :\: A) :e F. exact Hcompl A HA.
  claim HInter: B :/\: (Omega :\: A) :e F.
    exact field_closed_under_intersection Omega F B (Omega :\: A) Hfield HB HBcomplA.
  rewrite HBAeq.
  exact HInter.
}
claim Hdisj: Disjoint A (B :\: A).
{
  claim HsubEmpty: A :/\: (B :\: A) c= Empty.
  {
    let z. assume Hz.
    claim HzA: z :e A. exact binintersectE1 A (B :\: A) z Hz.
    claim HzNotA: z /:e A. exact setminusE2 B A z (binintersectE2 A (B :\: A) z Hz).
    exact FalseE (HzNotA HzA) (z :e Empty).
  }
  exact Empty_Subq_eq (A :/\: (B :\: A)) HsubEmpty.
}
claim Hunion: A :\/: (B :\: A) = B.
{
  apply set_ext.
  - prove A :\/: (B :\: A) c= B.
    let z. assume Hz.
    apply binunionE A (B :\: A) z Hz.
    + assume HzA: z :e A.
      exact Hab z HzA.
    + assume HzBA: z :e B :\: A.
      exact setminusE1 B A z HzBA.
  - prove B c= A :\/: (B :\: A).
    let z. assume HzB: z :e B.
    apply orE (z :e A) (z /:e A) (z :e A :\/: (B :\: A)).
    + assume HzA: z :e A.
      exact binunionI1 A (B :\: A) z HzA.
    + assume HzNotA: z /:e A.
      claim HzInDiff: z :e B :\: A. exact setminusI B A z HzB HzNotA.
      exact binunionI2 A (B :\: A) z HzInDiff.
    + exact xm (z :e A).
}
claim HPB: P B = P A + P (B :\: A).
{
  claim HeqPB: P (A :\/: (B :\: A)) = P B.
  { exact func_congr P (A :\/: (B :\: A)) B Hunion. }
  rewrite <- HeqPB.
  exact prob_finite_additivity Omega F P A (B :\: A) H HA HBA_in Hdisj.
}
claim HnonnegBA: 0 <= P (B :\: A).
{
  exact andER (P (B :\: A) :e real) (0 <= P (B :\: A)) (Hnonneg (B :\: A) HBA_in).
}
claim HPA_real: P A :e real.
{
  exact andEL (P A :e real) (0 <= P A) (Hnonneg A HA).
}
claim HPBA_real: P (B :\: A) :e real.
{
  exact andEL (P (B :\: A) :e real) (0 <= P (B :\: A)) (Hnonneg (B :\: A) HBA_in).
}
rewrite HPB.
exact real_zero_le_implies_add_le (P A) (P (B :\: A)) HnonnegBA.
Qed.

Theorem prob_complement :
  forall Omega F, forall P: set -> set, forall A,
    is_probability_measure Omega F P ->
    A :e F ->
    P (Omega :\: A) = 1 + - P A.
let Omega. let F. let P. let A.
assume H. assume HA.
claim Hsigma: is_sigma_field Omega F.
  exact prob_measure_is_sigma_field Omega F P H.
claim Hfield: is_field Omega F.
  exact sigma_field_is_field Omega F Hsigma.
claim Hrest: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
claim Hnonneg: forall X :e F, P X :e real /\ 0 <= P X.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) Hrest.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              Hfield.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
claim Hcompl: forall X :e F, (Omega :\: X) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim Hsub: forall X :e F, X c= Omega.
  exact andEL (forall A :e F, A c= Omega) (Omega :e F) H12.
claim HAc: (Omega :\: A) :e F. exact Hcompl A HA.
claim Hdisj: Disjoint A (Omega :\: A).
{
  claim HsubEmpty: A :/\: (Omega :\: A) c= Empty.
  {
    let z. assume Hz.
    claim HzA: z :e A. exact binintersectE1 A (Omega :\: A) z Hz.
    claim HzNotA: z /:e A. exact setminusE2 Omega A z (binintersectE2 A (Omega :\: A) z Hz).
    exact FalseE (HzNotA HzA) (z :e Empty).
  }
  exact Empty_Subq_eq (A :/\: (Omega :\: A)) HsubEmpty.
}
claim Hunion: A :\/: (Omega :\: A) = Omega.
{
  apply set_ext.
  - prove A :\/: (Omega :\: A) c= Omega.
    let z. assume Hz.
    apply binunionE A (Omega :\: A) z Hz.
    + assume HzA: z :e A.
      exact Hsub A HA z HzA.
    + assume Hzc: z :e Omega :\: A.
      exact setminusE1 Omega A z Hzc.
  - prove Omega c= A :\/: (Omega :\: A).
    let z. assume HzOmega: z :e Omega.
    apply orE (z :e A) (z /:e A) (z :e A :\/: (Omega :\: A)).
    + assume HzA: z :e A.
      exact binunionI1 A (Omega :\: A) z HzA.
    + assume HzNotA: z /:e A.
      claim HzComp: z :e Omega :\: A. exact setminusI Omega A z HzOmega HzNotA.
      exact binunionI2 A (Omega :\: A) z HzComp.
    + exact xm (z :e A).
}
claim Hsum: P Omega = P A + P (Omega :\: A).
{
  claim HeqPOmega: P (A :\/: (Omega :\: A)) = P Omega.
  { exact func_congr P (A :\/: (Omega :\: A)) Omega Hunion. }
  rewrite <- HeqPOmega.
  exact prob_finite_additivity Omega F P A (Omega :\: A) H HA HAc Hdisj.
}
claim Hrest1: P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))).
{
  exact andER (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) Hrest.
}
claim POmega1: P Omega = 1.
{
  exact andEL (P Omega = 1) (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) Hrest1.
}
claim HA_real: P A :e real. exact andEL (P A :e real) (0 <= P A) (Hnonneg A HA).
claim HComp_real: P (Omega :\: A) :e real. exact andEL (P (Omega :\: A) :e real) (0 <= P (Omega :\: A)) (Hnonneg (Omega :\: A) HAc).
claim Hsum1: 1 = P A + P (Omega :\: A).
{
  rewrite <- POmega1.
  exact Hsum.
}
claim Hcalc: 1 + - P A = P (Omega :\: A).
{
  exact real_add_left_cancel 1 (P A) (P (Omega :\: A)) Hsum1.
}
rewrite Hcalc.
reflexivity.
Qed.

Theorem prob_union_bound :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    P (A :\/: B) <= P A + P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB.
claim Hsigma: is_sigma_field Omega F.
  exact prob_measure_is_sigma_field Omega F P H.
claim Hfield: is_field Omega F.
  exact sigma_field_is_field Omega F Hsigma.
claim Hrest: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
claim Hnonneg: forall X :e F, P X :e real /\ 0 <= P X.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) Hrest.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              Hfield.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
claim Hcompl: forall X :e F, (Omega :\: X) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim Hsub: forall X :e F, X c= Omega.
  exact andEL (forall A :e F, A c= Omega) (Omega :e F) H12.
claim HBAeq: (B :\: A) = B :/\: (Omega :\: A).
{
  apply set_ext.
  - prove B :\: A c= B :/\: (Omega :\: A).
    let z. assume Hz.
    apply binintersectI.
    + exact setminusE1 B A z Hz.
    + claim HzOmega: z :e Omega. exact Hsub B HB z (setminusE1 B A z Hz).
      exact setminusI Omega A z HzOmega (setminusE2 B A z Hz).
  - prove B :/\: (Omega :\: A) c= B :\: A.
    let z. assume Hz.
    claim HzB: z :e B. exact binintersectE1 B (Omega :\: A) z Hz.
    claim HzNotA: z /:e A. exact setminusE2 Omega A z (binintersectE2 B (Omega :\: A) z Hz).
    exact setminusI B A z HzB HzNotA.
}
claim HBA_in: (B :\: A) :e F.
{
  claim HBcomplA: (Omega :\: A) :e F. exact Hcompl A HA.
  claim HInter: B :/\: (Omega :\: A) :e F.
    exact field_closed_under_intersection Omega F B (Omega :\: A) Hfield HB HBcomplA.
  rewrite HBAeq.
  exact HInter.
}
claim Hdisj: Disjoint A (B :\: A).
{
  claim HsubEmpty: A :/\: (B :\: A) c= Empty.
  {
    let z. assume Hz.
    claim HzA: z :e A. exact binintersectE1 A (B :\: A) z Hz.
    claim HzNotA: z /:e A. exact setminusE2 B A z (binintersectE2 A (B :\: A) z Hz).
    exact FalseE (HzNotA HzA) (z :e Empty).
  }
  exact Empty_Subq_eq (A :/\: (B :\: A)) HsubEmpty.
}
claim Hunion: A :\/: (B :\: A) = A :\/: B.
{
  apply set_ext.
  - prove A :\/: (B :\: A) c= A :\/: B.
    let z. assume Hz.
    apply binunionE A (B :\: A) z Hz.
    + assume HzA: z :e A. exact binunionI1 A B z HzA.
    + assume HzDiff: z :e B :\: A.
      exact binunionI2 A B z (setminusE1 B A z HzDiff).
  - prove A :\/: B c= A :\/: (B :\: A).
    let z. assume Hz.
    apply binunionE A B z Hz.
    + assume HzA: z :e A. exact binunionI1 A (B :\: A) z HzA.
    + assume HzB: z :e B.
      apply orE (z :e A) (z /:e A) (z :e A :\/: (B :\: A)).
      * assume HzA: z :e A. exact binunionI1 A (B :\: A) z HzA.
      * assume HzNotA: z /:e A.
        claim HzDiff: z :e B :\: A. exact setminusI B A z HzB HzNotA.
        exact binunionI2 A (B :\: A) z HzDiff.
      * exact xm (z :e A).
}
claim Hsum: P (A :\/: B) = P A + P (B :\: A).
{
  claim HeqUnion: P (A :\/: (B :\: A)) = P (A :\/: B).
  { exact func_congr P (A :\/: (B :\: A)) (A :\/: B) Hunion. }
  rewrite <- HeqUnion.
  exact prob_finite_additivity Omega F P A (B :\: A) H HA HBA_in Hdisj.
}
claim Hsubset: B :\: A c= B.
{
  let z. assume HzDiff: z :e B :\: A.
  exact setminusE1 B A z HzDiff.
}
claim Hmonob: P (B :\: A) <= P B.
{
  exact prob_monotone Omega F P (B :\: A) B H HBA_in HB Hsubset.
}
claim HPA_real: P A :e real. exact andEL (P A :e real) (0 <= P A) (Hnonneg A HA).
claim HPBA_real: P (B :\: A) :e real. exact andEL (P (B :\: A) :e real) (0 <= P (B :\: A)) (Hnonneg (B :\: A) HBA_in).
claim HPB_real: P B :e real. exact andEL (P B :e real) (0 <= P B) (Hnonneg B HB).
claim Hinter: P (B :\: A) + P A <= P B + P A.
{
  exact real_le_add_r (P (B :\: A)) (P B) (P A) Hmonob.
}
claim Hsum': P (A :\/: B) = P (B :\: A) + P A.
{
  rewrite Hsum.
  rewrite real_add_comm (P A) (P (B :\: A)).
  reflexivity.
}
rewrite Hsum'.
rewrite <- real_add_comm (P B) (P A).
exact Hinter.
Qed.

Definition conditional_prob : set -> (set -> set) -> set -> set -> set :=
  fun Omega P A B =>
    If_i (0 < P B) (P (A :/\: B) :/: P B) 0.

Axiom conditional_prob_real :
  forall Omega, forall P: set -> set, forall A B, conditional_prob Omega P A B :e real.

Theorem product_rule :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    P (A :/\: B) = P B * conditional_prob Omega P A B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hp.

claim EqCond: conditional_prob Omega P A B = P (A :/\: B) :/: P B.
{
  claim Def: conditional_prob Omega P A B = If_i (0 < P B) (P (A :/\: B) :/: P B) 0. { reflexivity. }
  rewrite Def.
  rewrite (If_i_1 (0 < P B) (P (A :/\: B) :/: P B) 0 Hp).
  reflexivity.
}

rewrite EqCond.
claim Hsigma: is_sigma_field Omega F.
  exact prob_measure_is_sigma_field Omega F P H.
claim Hfield: is_field Omega F.
  exact sigma_field_is_field Omega F Hsigma.
claim Hrest: (forall A :e F, P A :e real /\ 0 <= P A)
             /\ (P Omega = 1 /\ (P Empty = 0
             /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F)
              ((forall A :e F, P A :e real /\ 0 <= P A)
              /\ (P Omega = 1 /\ (P Empty = 0
              /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))))
              H.
claim Hnonneg: forall X :e F, P X :e real /\ 0 <= P X.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A)
              (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))
              Hrest.
claim HAnB_in: (A :/\: B) :e F.
  exact field_closed_under_intersection Omega F A B Hfield HA HB.
claim HPAB_real: P (A :/\: B) :e real.
  exact andEL (P (A :/\: B) :e real) (0 <= P (A :/\: B)) (Hnonneg (A :/\: B) HAnB_in).
claim HPB_real: P B :e real.
  exact andEL (P B :e real) (0 <= P B) (Hnonneg B HB).
claim HPB_neq0: P B <> 0.
  exact real_pos_neq0 (P B) Hp.
claim Hmuldiv: P B * (P (A :/\: B) :/: P B) = P (A :/\: B).
  exact real_mul_div_left (P (A :/\: B)) HPAB_real (P B) HPB_real HPB_neq0.
exact eq_sym (P B * (P (A :/\: B) :/: P B)) (P (A :/\: B)) Hmuldiv.
Qed.

Theorem bayes_theorem :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P A ->
    0 < P B ->
    conditional_prob Omega P A B = (conditional_prob Omega P B A * P A) :/: (P B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpA. assume HpB.
claim Eq1: P (A :/\: B) = P B * conditional_prob Omega P A B.
  exact product_rule Omega F P A B H HA HB HpB.
claim Eq2raw: P (B :/\: A) = P A * conditional_prob Omega P B A.
  exact product_rule Omega F P B A H HB HA HpA.
claim Eq2: P (A :/\: B) = P A * conditional_prob Omega P B A.
  {
    rewrite <- Eq2raw.
    rewrite binintersect_com.
    reflexivity.
  }
claim Heq: P B * conditional_prob Omega P A B = P A * conditional_prob Omega P B A.
  { rewrite <- Eq1. exact Eq2. }
claim HPB_neq0: P B <> 0.
  exact real_pos_neq0 (P B) HpB.
claim Hrest: (forall A :e F, P A :e real /\ 0 <= P A)
             /\ (P Omega = 1 /\ (P Empty = 0
             /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F)
              ((forall A :e F, P A :e real /\ 0 <= P A)
              /\ (P Omega = 1 /\ (P Empty = 0
              /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))))
              H.
claim Hnonneg: forall X :e F, P X :e real /\ 0 <= P X.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A)
              (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))
              Hrest.
claim HPB_real: P B :e real.
  exact andEL (P B :e real) (0 <= P B) (Hnonneg B HB).
claim HPA_real: P A :e real.
  exact andEL (P A :e real) (0 <= P A) (Hnonneg A HA).
claim Hcomm: conditional_prob Omega P A B * P B = P B * conditional_prob Omega P A B.
  exact real_mul_comm (conditional_prob Omega P A B) (P B).
claim Heq': conditional_prob Omega P A B * P B = P A * conditional_prob Omega P B A.
  { rewrite Hcomm. exact Heq. }
claim Hdiv: conditional_prob Omega P A B = (conditional_prob Omega P A B * P B) :/: P B.
  exact eq_sym ((conditional_prob Omega P A B * P B) :/: P B) (conditional_prob Omega P A B) (real_mul_div_cancel_right (conditional_prob Omega P A B) (conditional_prob_real Omega P A B) (P B) HPB_real HPB_neq0).
rewrite Hdiv.
rewrite Heq'.
rewrite real_mul_comm (conditional_prob Omega P B A) (P A).
reflexivity.
Qed.

Theorem total_probability_binary :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    0 < P (Omega :\: B) ->
    P A = P (A :/\: B) + P (A :/\: (Omega :\: B)).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpB. assume HpBc.
claim Hsigma: is_sigma_field Omega F.
  exact prob_measure_is_sigma_field Omega F P H.
claim Hfield: is_field Omega F.
  exact sigma_field_is_field Omega F Hsigma.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              Hfield.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
claim HsubAll: forall X :e F, X c= Omega.
  exact andEL (forall A :e F, A c= Omega) (Omega :e F) H12.
claim Hcompl: forall X :e F, (Omega :\: X) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim HrestP: (forall A :e F, P A :e real /\ 0 <= P A)
             /\ (P Omega = 1 /\ (P Empty = 0
             /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F)
              ((forall A :e F, P A :e real /\ 0 <= P A)
              /\ (P Omega = 1 /\ (P Empty = 0
              /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))))
              H.
claim Hnonneg: forall X :e F, P X :e real /\ 0 <= P X.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A)
              (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))
              HrestP.
claim HBc_in: (Omega :\: B) :e F.
  exact Hcompl B HB.
claim HA_inter_B: (A :/\: B) :e F.
  exact field_closed_under_intersection Omega F A B Hfield HA HB.
claim HA_inter_Bc: (A :/\: (Omega :\: B)) :e F.
  exact field_closed_under_intersection Omega F A (Omega :\: B) Hfield HA HBc_in.
claim Hdisj: Disjoint (A :/\: B) (A :/\: (Omega :\: B)).
{
  claim Hsub: (A :/\: B) :/\: (A :/\: (Omega :\: B)) c= Empty.
  {
    let z. assume Hz.
    claim HzInAB: z :e A :/\: B.
      exact binintersectE1 (A :/\: B) (A :/\: (Omega :\: B)) z Hz.
    claim HzB: z :e B.
      exact binintersectE2 A B z HzInAB.
    claim HzNotB: z /:e B.
    {
      claim HzInABc: z :e A :/\: (Omega :\: B).
        exact binintersectE2 (A :/\: B) (A :/\: (Omega :\: B)) z Hz.
      claim HzInBc: z :e Omega :\: B.
        exact binintersectE2 A (Omega :\: B) z HzInABc.
      exact setminusE2 Omega B z HzInBc.
    }
    exact FalseE (HzNotB HzB) (z :e Empty).
  }
  exact Empty_Subq_eq ((A :/\: B) :/\: (A :/\: (Omega :\: B))) Hsub.
}
claim Hunion: (A :/\: B) :\/: (A :/\: (Omega :\: B)) = A.
{
  apply set_ext.
  - let z. assume Hz.
    apply binunionE (A :/\: B) (A :/\: (Omega :\: B)) z Hz.
    + assume Hz1: z :e A :/\: B.
      exact binintersectE1 A B z Hz1.
    + assume Hz2: z :e A :/\: (Omega :\: B).
      exact binintersectE1 A (Omega :\: B) z Hz2.
  - let z. assume HzA: z :e A.
    apply orE (z :e B) (z /:e B) (z :e (A :/\: B) :\/: (A :/\: (Omega :\: B))).
    + assume HzB: z :e B.
      apply binunionI1 (A :/\: B) (A :/\: (Omega :\: B)) z.
      exact binintersectI A B z HzA HzB.
    + assume HzNotB: z /:e B.
      claim HzBc: z :e Omega :\: B.
      {
        claim HzOmega: z :e Omega.
          exact HsubAll A HA z HzA.
        exact setminusI Omega B z HzOmega HzNotB.
      }
      apply binunionI2 (A :/\: B) (A :/\: (Omega :\: B)) z.
      exact binintersectI A (Omega :\: B) z HzA HzBc.
    + exact xm (z :e B).
}
claim Hfinadd: P ((A :/\: B) :\/: (A :/\: (Omega :\: B))) = P (A :/\: B) + P (A :/\: (Omega :\: B)).
  exact prob_finite_additivity Omega F P (A :/\: B) (A :/\: (Omega :\: B)) H HA_inter_B HA_inter_Bc Hdisj.
claim HfinaddA: P A = P (A :/\: B) + P (A :/\: (Omega :\: B)).
{
  claim HPcongr: P ((A :/\: B) :\/: (A :/\: (Omega :\: B))) = P A.
    exact func_congr P ((A :/\: B) :\/: (A :/\: (Omega :\: B))) A Hunion.
  exact eq_trans (P A)
                 (P ((A :/\: B) :\/: (A :/\: (Omega :\: B))))
                 (P (A :/\: B) + P (A :/\: (Omega :\: B)))
                 (eq_sym (P ((A :/\: B) :\/: (A :/\: (Omega :\: B)))) (P A) HPcongr)
                 Hfinadd.
}
exact HfinaddA.
Qed.

Theorem total_probability_binary_conditional :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    0 < P (Omega :\: B) ->
    P A = conditional_prob Omega P A B * P B + conditional_prob Omega P A (Omega :\: B) * P (Omega :\: B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpB. assume HpBc.
claim Hsigma: is_sigma_field Omega F.
  exact prob_measure_is_sigma_field Omega F P H.
claim Hfield: is_field Omega F.
  exact sigma_field_is_field Omega F Hsigma.
claim Hrest: (forall A :e F, P A :e real /\ 0 <= P A)
             /\ (P Omega = 1 /\ (P Empty = 0
             /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F)
              ((forall A :e F, P A :e real /\ 0 <= P A)
              /\ (P Omega = 1 /\ (P Empty = 0
              /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))))
              H.
claim Hnonneg: forall X :e F, P X :e real /\ 0 <= P X.
  exact andEL (forall A :e F, P A :e real /\ 0 <= P A)
              (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))
              Hrest.
claim HBc_in: (Omega :\: B) :e F.
  exact field_complement_closed Omega F B Hfield HB.
claim HPB_real: P B :e real.
  exact prob_value_real Omega F P H B HB.
claim HPBc_real: P (Omega :\: B) :e real.
  exact prob_value_real Omega F P H (Omega :\: B) HBc_in.
claim HPAB_real: P (A :/\: B) :e real.
  exact prob_value_real Omega F P H (A :/\: B) (field_closed_under_intersection Omega F A B Hfield HA HB).
claim HPABc_real: P (A :/\: (Omega :\: B)) :e real.
  exact prob_value_real Omega F P H (A :/\: (Omega :\: B)) (field_closed_under_intersection Omega F A (Omega :\: B) Hfield HA HBc_in).
claim Eqbase: P A = P (A :/\: B) + P (A :/\: (Omega :\: B)).
  exact total_probability_binary Omega F P A B H HA HB HpB HpBc.
claim EqCondB: conditional_prob Omega P A B = P (A :/\: B) :/: P B.
  {
    claim Def: conditional_prob Omega P A B = If_i (0 < P B) (P (A :/\: B) :/: P B) 0. { reflexivity. }
    rewrite Def.
    rewrite (If_i_1 (0 < P B) (P (A :/\: B) :/: P B) 0 HpB).
    reflexivity.
  }
claim EqCondBc: conditional_prob Omega P A (Omega :\: B) = P (A :/\: (Omega :\: B)) :/: P (Omega :\: B).
  {
    claim Def: conditional_prob Omega P A (Omega :\: B) = If_i (0 < P (Omega :\: B)) (P (A :/\: (Omega :\: B)) :/: P (Omega :\: B)) 0. { reflexivity. }
    rewrite Def.
    rewrite (If_i_1 (0 < P (Omega :\: B)) (P (A :/\: (Omega :\: B)) :/: P (Omega :\: B)) 0 HpBc).
    reflexivity.
  }
claim HPB_neq0: P B <> 0.
  exact real_pos_neq0 (P B) HpB.
claim HPBc_neq0: P (Omega :\: B) <> 0.
  exact real_pos_neq0 (P (Omega :\: B)) HpBc.
claim HmulB: conditional_prob Omega P A B * P B = P (A :/\: B).
  {
    rewrite EqCondB.
    rewrite real_mul_comm.
    exact real_mul_div_left (P (A :/\: B)) HPAB_real (P B) HPB_real HPB_neq0.
  }
claim HmulBc: conditional_prob Omega P A (Omega :\: B) * P (Omega :\: B) = P (A :/\: (Omega :\: B)).
  {
    rewrite EqCondBc.
    rewrite real_mul_comm.
    exact real_mul_div_left (P (A :/\: (Omega :\: B))) HPABc_real (P (Omega :\: B)) HPBc_real HPBc_neq0.
  }
rewrite Eqbase.
rewrite <- HmulB.
rewrite <- HmulBc.
reflexivity.
Qed.

Definition independent_events : set -> (set -> set) -> set -> set -> prop :=
  fun Omega P A B =>
    P (A :/\: B) = P A * P B.

Theorem independent_events_elim :
  forall Omega, forall P: set -> set, forall A B,
    independent_events Omega P A B ->
    P (A :/\: B) = P A * P B.
let Omega. let P. let A. let B. assume H. exact H. Qed.

Theorem independent_events_intro :
  forall Omega, forall P: set -> set, forall A B,
    P (A :/\: B) = P A * P B ->
    independent_events Omega P A B.
let Omega. let P. let A. let B. assume H. exact H. Qed.

Definition independent_events_3 : set -> (set -> set) -> set -> set -> set -> prop :=
  fun Omega P A B C =>
    independent_events Omega P A B
    /\ independent_events Omega P A C
    /\ independent_events Omega P B C
    /\ P (A :/\: B :/\: C) = P A * P B * P C.

Theorem independence_sym :
  forall Omega, forall P: set -> set, forall A B,
    independent_events Omega P A B ->
    independent_events Omega P B A.
let Omega. let P. let A. let B.
assume H.
claim Heq: P (A :/\: B) = P A * P B.
  exact independent_events_elim Omega P A B H.
claim Hgoal: P (B :/\: A) = P B * P A.
{
  rewrite binintersect_com.
  rewrite real_mul_comm.
  exact Heq.
}
exact independent_events_intro Omega P B A Hgoal.
Qed.

Theorem independent_implies_conditional :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    independent_events Omega P A B ->
    conditional_prob Omega P A B = P A.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hp. assume Hind.
claim EqCond: conditional_prob Omega P A B = P (A :/\: B) :/: P B.
  {
    claim Def: conditional_prob Omega P A B = If_i (0 < P B) (P (A :/\: B) :/: P B) 0. { reflexivity. }
    rewrite Def.
    rewrite (If_i_1 (0 < P B) (P (A :/\: B) :/: P B) 0 Hp).
    reflexivity.
  }
claim HPB_neq0: P B <> 0.
  exact real_pos_neq0 (P B) Hp.
claim HPA_real: P A :e real.
  exact prob_value_real Omega F P H A HA.
claim HPB_real: P B :e real.
  exact prob_value_real Omega F P H B HB.
claim HindEq: P (A :/\: B) = P A * P B.
  exact independent_events_elim Omega P A B Hind.
rewrite EqCond.
rewrite HindEq.
exact real_mul_div_cancel_right (P A) HPA_real (P B) HPB_real HPB_neq0.
Qed.

Theorem independent_complement :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    independent_events Omega P A B ->
    independent_events Omega P A (Omega :\: B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hind.
claim Hsigma: is_sigma_field Omega F.
  exact prob_measure_is_sigma_field Omega F P H.
claim Hfield: is_field Omega F.
  exact sigma_field_is_field Omega F Hsigma.
claim HBc_in: (Omega :\: B) :e F.
  exact field_complement_closed Omega F B Hfield HB.
claim HsubAll: forall X :e F, X c= Omega.
{
  let X. assume HX.
  exact field_subset Omega F X Hfield HX.
}
claim HA_inter_B: (A :/\: B) :e F.
  exact field_closed_under_intersection Omega F A B Hfield HA HB.
claim HA_inter_Bc: (A :/\: (Omega :\: B)) :e F.
  exact field_closed_under_intersection Omega F A (Omega :\: B) Hfield HA HBc_in.
claim Hdisj: Disjoint (A :/\: B) (A :/\: (Omega :\: B)).
  {
    claim Hsub: (A :/\: B) :/\: (A :/\: (Omega :\: B)) c= Empty.
    {
      let z. assume Hz.
      claim HzInAB: z :e A :/\: B.
        exact binintersectE1 (A :/\: B) (A :/\: (Omega :\: B)) z Hz.
      claim HzB: z :e B.
        exact binintersectE2 A B z HzInAB.
      claim HzNotB: z /:e B.
      {
        claim HzInABc: z :e A :/\: (Omega :\: B).
          exact binintersectE2 (A :/\: B) (A :/\: (Omega :\: B)) z Hz.
        claim HzInBc: z :e Omega :\: B.
          exact binintersectE2 A (Omega :\: B) z HzInABc.
        exact setminusE2 Omega B z HzInBc.
      }
      exact FalseE (HzNotB HzB) (z :e Empty).
    }
  exact Empty_Subq_eq ((A :/\: B) :/\: (A :/\: (Omega :\: B))) Hsub.
}
claim Hunion: (A :/\: B) :\/: (A :/\: (Omega :\: B)) = A.
{
  apply set_ext.
  - let z. assume Hz.
    apply binunionE (A :/\: B) (A :/\: (Omega :\: B)) z Hz.
    + assume Hz1: z :e A :/\: B.
      exact binintersectE1 A B z Hz1.
    + assume Hz2: z :e A :/\: (Omega :\: B).
      exact binintersectE1 A (Omega :\: B) z Hz2.
  - let z. assume HzA: z :e A.
    apply orE (z :e B) (z /:e B) (z :e (A :/\: B) :\/: (A :/\: (Omega :\: B))).
    + assume HzB: z :e B.
      apply binunionI1 (A :/\: B) (A :/\: (Omega :\: B)) z.
      exact binintersectI A B z HzA HzB.
    + assume HzNotB: z /:e B.
      claim HzOmega: z :e Omega.
        exact HsubAll A HA z HzA.
      claim HzBc: z :e Omega :\: B.
        exact setminusI Omega B z HzOmega HzNotB.
      apply binunionI2 (A :/\: B) (A :/\: (Omega :\: B)) z.
      exact binintersectI A (Omega :\: B) z HzA HzBc.
    + exact xm (z :e B).
}
claim Hfinadd: P A = P (A :/\: B) + P (A :/\: (Omega :\: B)).
{
  claim Hsum: P ((A :/\: B) :\/: (A :/\: (Omega :\: B))) = P (A :/\: B) + P (A :/\: (Omega :\: B)).
    exact prob_finite_additivity Omega F P (A :/\: B) (A :/\: (Omega :\: B)) H HA_inter_B HA_inter_Bc Hdisj.
  claim HPcongr: P ((A :/\: B) :\/: (A :/\: (Omega :\: B))) = P A.
    exact func_congr P ((A :/\: B) :\/: (A :/\: (Omega :\: B))) A Hunion.
  exact eq_trans (P A)
                 (P ((A :/\: B) :\/: (A :/\: (Omega :\: B))))
                 (P (A :/\: B) + P (A :/\: (Omega :\: B)))
                 (eq_sym (P ((A :/\: B) :\/: (A :/\: (Omega :\: B)))) (P A) HPcongr)
                 Hsum.
}
claim HPA_real: P A :e real.
  exact prob_value_real Omega F P H A HA.
claim HPB_real: P B :e real.
  exact prob_value_real Omega F P H B HB.
claim HindEq: P (A :/\: B) = P A * P B.
  exact independent_events_elim Omega P A B Hind.
claim HPBc: P (Omega :\: B) = 1 + - (P B).
  exact prob_complement Omega F P B H HB.
claim Hleft: P A + - (P (A :/\: B)) = P (A :/\: (Omega :\: B)).
{
  exact real_add_left_cancel (P A) (P (A :/\: B)) (P (A :/\: (Omega :\: B))) Hfinadd.
}
claim Hright: P A + - (P A * P B) = P A * (1 + - (P B)).
{
  rewrite real_mul_add_distr.
  rewrite real_mul_one_r.
  rewrite real_mul_neg.
  reflexivity.
}
claim Htarget: P (A :/\: (Omega :\: B)) = P A * P (Omega :\: B).
{
  rewrite <- Hleft.
  rewrite HindEq.
  rewrite HPBc.
  exact Hright.
}
exact independent_events_intro Omega P A (Omega :\: B) Htarget.
Qed.

Theorem power_is_field :
  forall Omega, is_field Omega (Power Omega).
let Omega.
set F := Power Omega.
apply andI (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
           (forall A B, A :e F -> B :e F -> (A :\/: B) :e F).
- apply andI (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
             (forall A :e F, (Omega :\: A) :e F).
  - apply andI ((forall A :e F, A c= Omega) /\ Omega :e F)
               (Empty :e F).
    + apply andI (forall A :e F, A c= Omega)
                 (Omega :e F).
      * let A.
        assume HA: A :e F.
        exact PowerE Omega A HA.
      * exact PowerI Omega Omega (Subq_ref Omega).
    + exact PowerI Omega Empty (Subq_Empty Omega).
  - let A.
    assume HA: A :e F.
    exact PowerI Omega (Omega :\: A) (setminus_Subq Omega A).
- let A. let B.
  assume HA: A :e F.
  assume HB: B :e F.
  claim HAsub: A c= Omega.
    exact PowerE Omega A HA.
  claim HBsub: B c= Omega.
    exact PowerE Omega B HB.
  exact PowerI Omega (A :\/: B) (binunion_Subq_min A B Omega HAsub HBsub).
Qed.

Theorem power_is_sigma_field :
  forall Omega, is_sigma_field Omega (Power Omega).
let Omega.
set F := Power Omega.
apply andI (is_field Omega F)
           (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F).
- exact power_is_field Omega.
- let f.
  assume Hf: forall n :e omega, f n :e F.
  apply PowerI.
  prove bigcup_nat f c= Omega.
  let x.
  assume Hx: x :e bigcup_nat f.
  claim BigDef: bigcup_nat f = Union {f n|n :e omega}.
  { reflexivity. }
  claim HxU: x :e Union {f n|n :e omega}.
  {
    rewrite <- BigDef.
    exact Hx.
  }
  apply (UnionE_impred {f n|n :e omega} x HxU).
  let Y.
  assume HxY: x :e Y.
  assume HY: Y :e {f n|n :e omega}.
  apply (ReplE_impred omega f Y HY).
  let n.
  assume Hn: n :e omega.
  assume HYeq: Y = f n.
  claim HfnSub: f n c= Omega.
  {
    exact PowerE Omega (f n) (Hf n Hn).
  }
  claim Hxfn: x :e f n.
  {
    rewrite <- HYeq.
    exact HxY.
  }
  exact HfnSub x Hxfn.
Qed.
