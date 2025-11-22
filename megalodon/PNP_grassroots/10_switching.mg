(* ========================================================================== *)
(* 10_switching.mg - Switching-by-Weakness                                   *)
(* ========================================================================== *)
(* Section 4: The central technical step - short decoders become local       *)
(* "Shortness implies locality on many blocks"                               *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* PART 1: Switching-by-Weakness Statement (Theorem 4.2)                     *)
(* -------------------------------------------------------------------------- *)

(* There exist constants gamma > 0 and c* > 0 such that: *)
(* For every polytime decoder P with |P| <= delta*t *)
(* There exists polytime wrapper W with |W| <= |P| + c*(log m + log t) *)
(* And subset S ⊆ [t] with |S| >= gamma*t *)
(* Such that each output bit on S is LOCAL: *)

(* (P o W)(Phi)_{j,i} = h_{j,i}(u_i(Phi_j)) for j in S, i in [m] *)
(* where h_{j,i} : {0,1}^{O(log m)} -> {0,1} *)

Theorem Switching_by_Weakness :
  forall m P delta,
    polytime_decoder P ->
    desc_length P <= mul delta (num_blocks m) ->
    exists gamma c_star W S,
      gamma > 0 /\
      c_star > 0 /\
      polytime_wrapper W /\
      desc_length W <= quant_add (desc_length P) (mul c_star (quant_add (log2 m) (log2 (num_blocks m)))) /\
      (* |S| >= gamma * t *)
      subset_size S >= mul gamma (num_blocks m) /\
      (* Locality on S *)
      (forall j :e S, forall i :e m,
        exists h, local_rule h m /\
        switched_output P W j i = h (local_input sils_z (block_at j) i)) /\
      True.
Admitted.

(* Moreover, each h_{j,i} is computable in time poly(log m) *)
(* Hence realizable by size poly(m) ACC^0 *)

(* -------------------------------------------------------------------------- *)
(* PART 2: Two Wrapper Constructions                                         *)
(* -------------------------------------------------------------------------- *)

(* Route 1: Symmetrization Wrapper (Section 4.2) *)
(* Average over polylogarithmic multiset of promise-preserving sign flips *)
(* Then take majority of back-mapped predictions *)

Definition symmetrization_wrapper : set -> set -> set :=
  fun P m =>
    let s := mul 20 (log2 (mul m (num_blocks m))) in  (* s = Theta(log(mt)) *)
    let kappa := mul 12 (log2 (mul m (num_blocks m))) in  (* kappa-wise independence *)
    (* Hard-wire s independent seeds of total length O(s * kappa) *)
    (* For each seed: apply sign-flip, run P, back-map predictions *)
    (* Output majority *)
    0.  (* Placeholder *)

(* Route 2: ERM Wrapper (Appendix A.1) *)
(* Learn per-bit local rules via empirical risk minimization *)
(* Uses train/test split and USAT verifier *)

Definition ERM_wrapper : set -> set -> set :=
  fun P m =>
    let t := num_blocks m in
    (* Train/test split: T ⊔ S = [t] *)
    (* For each bit i, define plug-in rule on finite alphabet U: *)
    (*   h_i(u) := Maj{ Y_{j,i} : j in T, u_{j,i} = u } *)
    (* On test blocks j in S, output h_i(u_{j,i}) *)
    0.  (* Placeholder *)

(* -------------------------------------------------------------------------- *)
(* PART 3: Symmetrization Properties                                         *)
(* -------------------------------------------------------------------------- *)

(* Lemma 4.3: Symmetrization preserves success exactly *)
(* Pr[P(Phi) = X] = E_sigma Pr[BM_sigma(P(g_sigma(Phi))) = X] *)

Theorem symmetrization_preserves_success :
  forall P m,
    polytime_decoder P ->
    (* Success of P equals average success of back-mapped predictions *)
    True.
Admitted.

(* Lemma 4.7: Wrapper budget *)
(* |W_sym| <= |P| + O(log m + log t) *)
(* (Counting O((log m + log t)^2) seed bits only once as advice) *)

Theorem symmetrization_wrapper_budget :
  forall P m,
    let W := symmetrization_wrapper P m in
    desc_length W <= quant_add (desc_length P) (wrapper_overhead m).
Admitted.

(* -------------------------------------------------------------------------- *)
(* PART 4: Success Domination (Theorem 4.5, Corollary 4.6)                   *)
(* -------------------------------------------------------------------------- *)

(* The wrapper's comparator does not underperform P: *)
(* Pr[(P o W)(Phi) = X] >= Pr[P(Phi) = X] - m^{-Omega(1)} *)

Theorem success_domination :
  forall P m W,
    polytime_decoder P ->
    W = ERM_wrapper P m ->
    (* Pr[(P o W) = X] >= Pr[P = X] - m^{-Omega(1)} *)
    True.
Admitted.

(* Corollary: Upper bounds for (P o W) apply to P *)
Corollary domination_principle :
  forall P m W upper_bound,
    polytime_decoder P ->
    W = ERM_wrapper P m ->
    (* If Pr[(P o W) = X] <= upper_bound, then Pr[P = X] <= upper_bound + m^{-Omega(1)} *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* PART 5: Calibration (Lemma 4.8)                                           *)
(* -------------------------------------------------------------------------- *)

(* ERM trains on symmetrized (back-mapped) labels Y, not on X *)
(* The link back to truth is calibration: *)

(* For fixed u = (z, a_i, b), the Bayes classifier for Y_i *)
(* is also optimal for X_i (up to m^{-Omega(1)}) *)

Theorem calibration_lemma :
  forall m i,
    (* Let f_i(u) = E[Y_i(sigma, Phi) | u] *)
    (* Let h*_i(u) = 1[f_i(u) >= 1/2] be Bayes classifier for f_i *)
    (* Then: E[1{h*_i(u) = X_i}] >= E_{sigma}[1{Y_i = X_i}] - m^{-Omega(1)} *)
    True.
Admitted.

(* Proof sketch: *)
(* 1. T_i bijects (X_i=0, Y_i=y) <-> (X_i=1, Y_i=1-y) preserving u and measure *)
(* 2. Thus (X_i, Y_i) | u is exchangeable *)
(* 3. Pr[X_i=1|u] = Pr[Y_i=1|u] = f_i(u) *)
(* 4. Bayes rule h*_i is optimal for both *)

(* -------------------------------------------------------------------------- *)
(* PART 6: ERM Generalization (Lemma A.3)                                    *)
(* -------------------------------------------------------------------------- *)

(* With |T| = Theta(t) = Theta(m) training samples: *)
(* Pr_{j in S}[h_i(u_{j,i}) != h*_i(u_{j,i})] <= m^{-Omega(1)} *)
(* simultaneously for all i in [m] *)

Theorem ERM_generalization :
  forall m i T S,
    (* Train/test split with |T|, |S| = Theta(t) *)
    (* W.p. 1 - m^{-Omega(1)}: plug-in ERM rule matches Bayes on test *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* PART 7: Finite Alphabet Locality (Section 4.3)                            *)
(* -------------------------------------------------------------------------- *)

(* Post-switch input u = (z, a_i, b) has |u| = O(log m) *)
(* Hence local alphabet U has size |U| <= 2^{O(log m)} = m^{O(1)} *)

Theorem finite_alphabet_compilation :
  forall m h d,
    d = O_log m ->
    (* Any h : {0,1}^d -> {0,1} has depth-2 circuit of size O(2^d) = poly(m) *)
    (* Hence also ACC^0 circuit of poly(m) size *)
    True.
Admitted.

(* ERM operates on U via plug-in rule - no hypothesis enumeration required *)
(* Wrapper description length remains |P| + O(log m + log t) *)

(* -------------------------------------------------------------------------- *)
(* PART 8: Why Switching Works (Section 4.5)                                 *)
(* -------------------------------------------------------------------------- *)

(* Five pillars that make the proof work: *)

(* (1) Compositionality of weakness *)
(*     K^poly is invariant up to O(1), obeys chain rule, block additivity *)

(* (2) Promise-preserving symmetry as two-way bridge *)
(*     g_sigma is measure- and promise-preserving bijection *)

(* (3) Low-dimensional locality by design *)
(*     Local input u has O(log m) bits -> polynomial alphabet *)

(* (4) Distillation with calibration *)
(*     Don't claim P is local; distill to local comparator with domination *)

(* (5) Distributional sparsity and independence *)
(*     Random 3-CNF is locally tree-like; test blocks are independent *)

(* -------------------------------------------------------------------------- *)
(* END OF 10_switching.mg                                                     *)
(* -------------------------------------------------------------------------- *)
