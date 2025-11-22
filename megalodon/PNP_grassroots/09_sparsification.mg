(* ========================================================================== *)
(* 09_sparsification.mg - Template Sparsification                            *)
(* ========================================================================== *)
(* Section 5.2-5.4: Sparsity at logarithmic radius                           *)
(* "Sparsity says: a fixed local chart is hit with probability m^{-Omega(1)}" *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* PART 1: Charts with Labels (Definition 5.5)                               *)
(* -------------------------------------------------------------------------- *)

(* A chart C = (P, psi) consists of: *)
(*   P: finite set of signed rooted radius-r patterns with VV labels (a_i, b) *)
(*   psi: P -> {0,1} decision rule *)

Definition Chart : set -> set :=
  fun r => {C | exists P psi,
    (* P is finite set of augmented patterns *)
    (* psi : P -> {0,1} *)
    C = (P, psi)}.

Definition chart_patterns : set -> set := fun C => ap C 0.
Definition chart_rule : set -> set := fun C => ap C 1.

(* (Phi, i) matches chart C if the local structure equals some P in C *)
Definition matches_chart : set -> set -> set -> set -> prop :=
  fun m Phi i C =>
    let r := mul c3_radius (log2 m) in
    exists P :e chart_patterns C,
      neighborhood_with_labels Phi i r = P.

(* Neighborhood with VV labels *)
Definition neighborhood_with_labels : set -> set -> set -> set :=
  fun Phi i r =>
    let Fh := instance_cnf Phi in
    let A := instance_matrix Phi in
    let b := instance_rhs Phi in
    (neighborhood Fh i r, vv_labels A b i).

(* -------------------------------------------------------------------------- *)
(* PART 2: High-Bias Region (Definition 5.6)                                 *)
(* -------------------------------------------------------------------------- *)

(* Fix epsilon > 0. The high-bias region of chart C is: *)
(* HB_eps(C) = { P in P : |Pr[X_i=1 | nbr=P] - 1/2| > epsilon } *)

Definition high_bias_region : set -> set -> set :=
  fun C eps =>
    {P :e chart_patterns C |
      (* |Pr[X_i = 1 | neighborhood = P] - 1/2| > epsilon *)
      True}.

(* C attains bias > eps on (Phi, i) if it matches some P in HB_eps(C) *)
Definition attains_high_bias : set -> set -> set -> set -> set -> prop :=
  fun m Phi i C eps =>
    exists P :e high_bias_region C eps,
      neighborhood_with_labels Phi i (mul c3_radius (log2 m)) = P.

(* -------------------------------------------------------------------------- *)
(* PART 3: Chart Probability Bound (Lemma 5.8)                               *)
(* -------------------------------------------------------------------------- *)

(* For any fixed chart C and epsilon > 0: *)
(* Pr[(Phi, i) matches some P in HB_eps(C)] <= m^{-beta''} *)

Theorem chart_probability_bound :
  forall m C eps,
    eps > 0 ->
    exists beta'',
      beta'' > 0 /\
      (* Pr[attains_high_bias m Phi i C eps] <= m^{-beta''} *)
      True.
Admitted.

(* Proof sketch: *)
(* 1. By Theorem 3.11(iii), each fixed signed pattern P has prob <= m^{-beta'} *)
(* 2. There are m^{O(1)} patterns of depth r = c_3 * log(m) *)
(* 3. VV labels contribute O(log m) entropy -> polynomial factor *)
(* 4. Union bound over finite HB_eps(C) gives the result *)

(* -------------------------------------------------------------------------- *)
(* PART 4: Few High-Bias Hits (Lemma 5.9)                                    *)
(* -------------------------------------------------------------------------- *)

(* For t = c_4 * m i.i.d. blocks and fixed chart C: *)
(* Number of high-bias blocks is o(t) with probability 1 - 2^{-Omega(m)} *)

Theorem few_high_bias_hits :
  forall m C eps,
    eps > 0 ->
    let t := num_blocks m in
    (* Expected number of high-bias blocks = t * m^{-beta''} = o(t) *)
    (* By Chernoff, concentrated around expectation *)
    True.
Admitted.

(* Proof: *)
(* For each j, indicator is Bernoulli with mean <= m^{-beta''} *)
(* Independence across blocks + Chernoff -> *)
(* Total count is O(t * m^{-beta''} + log m) w.p. 1 - 2^{-Omega(m)} *)
(* Since t = Theta(m) and beta'' > 1, this is o(t) *)

(* -------------------------------------------------------------------------- *)
(* PART 5: Template Sparsification (Theorem 5.10)                            *)
(* -------------------------------------------------------------------------- *)

(* Fix epsilon > 0 and let U be the local input alphabet *)
(* There exists beta > 1 such that for random (Phi, i): *)
(* Pr[exists u in U with u_i(Phi)=u and |Pr[X_i=1|u] - 1/2| > eps] <= m^{-beta} *)

Theorem template_sparsification :
  forall m eps,
    eps > 0 ->
    let U := local_alphabet_size m in
    exists beta,
      beta > 1 /\
      (* Pr[any u-value is eps-high-bias] <= m^{-beta} *)
      True.
Admitted.

(* Consequently, for t = c_4 * m blocks: *)
(* W.p. 1 - 2^{-Omega(m)}, at most o(t) blocks admit any high-bias u *)

Corollary sparsification_blocks :
  forall m eps,
    eps > 0 ->
    let t := num_blocks m in
    (* W.p. 1 - 2^{-Omega(m)}: *)
    (* |{j : exists i, u in U with high bias at (Phi_j, i)}| = o(t) *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* PART 6: Uniformity Over u-Measurable Rules (Remark A.16)                  *)
(* -------------------------------------------------------------------------- *)

(* The sparsification bound is UNIFORM over all u-measurable per-bit rules *)
(* Union bound ranges over: *)
(*   - Finite alphabet U (size m^{O(1)}) *)
(*   - Finite set of signed charts at radius r = c_3 * log(m) *)
(* No counting over hypothesis class required *)

Theorem uniform_sparsification :
  forall m,
    (* For ALL u-measurable rules h: {0,1}^{O(log m)} -> {0,1} *)
    (* The probability of high bias is uniformly bounded by m^{-Omega(1)} *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* PART 7: Many Locally Hard Blocks (Corollary 5.11)                         *)
(* -------------------------------------------------------------------------- *)

(* Combining Theorem 4.2 (Switching) with Theorem 5.10 (Sparsification): *)

(* For any polytime decoder P with |P| <= delta*t: *)
(* There exists wrapper W and set S with |S| >= gamma*t such that: *)
(* For all j in S, i in [m]: |Pr[(P o W)(Phi)_{j,i} = X_{j,i}] - 1/2| <= eps(m) *)

Corollary locally_hard_blocks :
  forall m P delta,
    desc_length P <= mul delta (num_blocks m) ->
    exists gamma eps_func W S,
      gamma > 0 /\
      (* eps_func(m) -> 0 as m -> infinity *)
      desc_length W <= quant_add (desc_length P) (wrapper_overhead m) /\
      (* |S| >= gamma * t *)
      (* For all j in S, i in [m]: per-bit near-randomness holds *)
      True.
Admitted.

(* This is the exact hypothesis needed for Section 6 product bounds *)

(* -------------------------------------------------------------------------- *)
(* END OF 09_sparsification.mg                                                *)
(* -------------------------------------------------------------------------- *)
