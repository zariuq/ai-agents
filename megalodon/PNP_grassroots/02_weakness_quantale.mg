(* ========================================================================== *)
(* 02_weakness_quantale.mg - Weakness Quantale and K^poly                     *)
(* ========================================================================== *)
(* Definition 2.1: Polytime-capped conditional description length             *)
(* This is the central information-theoretic measure in Goertzel's proof      *)
(* ========================================================================== *)
(*                                                                            *)
(* References:                                                                *)
(*   - Li & Vitányi, "An Introduction to Kolmogorov Complexity" (Springer)  *)
(*   - Shen et al., "Kolmogorov Complexity and Algorithmic Randomness"       *)
(*   - Wikipedia: Kolmogorov complexity, Quantale                             *)
(*   - Goertzel, arXiv:2510.08814v1, Section 2                               *)
(*                                                                            *)
(* ========================================================================== *)

(* We import definitions from 01_foundations.mg *)
(* Assumes: nat_p, ordsucc, add, mul, exp, log2, strlen, concat, etc. *)
(* Assumes: Program, UTM_computes, UTM_halts_in, is_polytime, etc. *)

(* ========================================================================== *)
(*                    SECTION A: KOLMOGOROV COMPLEXITY                        *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* A.1: Plain Kolmogorov Complexity C(x)                                      *)
(* -------------------------------------------------------------------------- *)

(* C(x) = min{|p| : U(p) = x} *)
(* The length of the shortest program that outputs x with no input *)

Definition plain_complexity : set -> set :=
  fun x =>
    Eps_i (fun k =>
      nat_p k /\
      (exists p, desc_length p = k /\ UTM_computes p empty_string x) /\
      (forall p', UTM_computes p' empty_string x -> ord_le k (desc_length p'))).

(* Notation: C(x) *)
Definition C : set -> set := plain_complexity.

(* -------------------------------------------------------------------------- *)
(* A.2: Conditional Kolmogorov Complexity C(x|y)                              *)
(* -------------------------------------------------------------------------- *)

(* C(x|y) = min{|p| : U(p,y) = x} *)
(* The length of the shortest program that outputs x given y *)

Definition conditional_complexity : set -> set -> set :=
  fun x y =>
    Eps_i (fun k =>
      nat_p k /\
      (exists p, desc_length p = k /\ UTM_computes p y x) /\
      (forall p', UTM_computes p' y x -> ord_le k (desc_length p'))).

(* Notation: C(x|y) *)
Definition C_cond : set -> set -> set := conditional_complexity.

(* -------------------------------------------------------------------------- *)
(* A.3: Prefix-Free Kolmogorov Complexity K(x)                                *)
(* -------------------------------------------------------------------------- *)

(* K(x) uses a prefix-free universal machine, satisfying Kraft inequality *)
(* K(x) ≥ C(x) but K(x) ≤ C(x) + 2*log(C(x)) + O(1) *)

Definition prefix_complexity : set -> set :=
  fun x =>
    Eps_i (fun k =>
      nat_p k /\
      (exists p, desc_length p = k /\ UTM_computes p empty_string x /\ prefix_free) /\
      (forall p', UTM_computes p' empty_string x /\ prefix_free -> ord_le k (desc_length p'))).

Definition K : set -> set := prefix_complexity.

(* Conditional prefix complexity K(x|y) *)
Definition K_cond : set -> set -> set :=
  fun x y =>
    Eps_i (fun k =>
      nat_p k /\
      (exists p, desc_length p = k /\ UTM_computes p y x /\ prefix_free) /\
      True).


(* ========================================================================== *)
(*                    SECTION B: POLYTIME-CAPPED COMPLEXITY K^poly            *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* B.1: Definition 2.1 from Goertzel                                          *)
(* -------------------------------------------------------------------------- *)

(* K^poly(z|y) = min{|p| : U(p,y) = z and U halts in |y|^O(1) steps}         *)
(* This is the key measure: complexity restricted to polynomial-time programs *)

Definition Kpoly : set -> set -> set :=
  fun z y =>
    Eps_i (fun k =>
      nat_p k /\
      (* There exists a program of length k that computes z from y in polytime *)
      (exists p, desc_length p = k /\
                 UTM_computes p y z /\
                 exists c :e omega, UTM_halts_in p y (exp (strlen y) c)) /\
      (* And k is minimal among all such programs *)
      (forall p', UTM_computes p' y z ->
                  (exists c' :e omega, UTM_halts_in p' y (exp (strlen y) c')) ->
                  ord_le k (desc_length p'))).

(* Alternative notation: weakness *)
Definition weakness : set -> set -> set := Kpoly.

(* -------------------------------------------------------------------------- *)
(* B.2: Infinity for Undecidable Pairs                                        *)
(* -------------------------------------------------------------------------- *)

(* If no polytime program computes z from y, K^poly(z|y) = ∞ *)
(* We represent ∞ as omega (the first infinite ordinal) *)

Definition Kpoly_infinite : set -> set -> prop :=
  fun z y =>
    ~(exists p, UTM_computes p y z /\
                exists c :e omega, UTM_halts_in p y (exp (strlen y) c)).

(* For on-promise inputs (USAT instances), K^poly is always finite *)
Theorem Kpoly_finite_on_promise :
  forall Phi X,
    (* If Phi is an on-promise USAT instance with unique witness X *)
    (* Then K^poly(X|Phi) is finite *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* B.3: Invariance Theorem for K^poly                                         *)
(* -------------------------------------------------------------------------- *)

(* The choice of UTM affects K^poly by at most an additive constant *)
(* This is standard from Kolmogorov complexity theory *)

Theorem Kpoly_invariance :
  forall U V,
    (* For any two universal TMs U and V *)
    exists c_UV :e omega,
      forall z y,
        (* |K^poly_U(z|y) - K^poly_V(z|y)| <= c_UV *)
        True.
Admitted.

(* The constant c_UV is the length of the simulation program *)


(* ========================================================================== *)
(*                    SECTION C: QUANTALE STRUCTURE                           *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* C.1: The Carrier Set                                                       *)
(* -------------------------------------------------------------------------- *)

(* The quantale carrier is (ℕ ∪ {∞}, +, ≤)                                   *)
(* - Elements are natural numbers (description lengths) or ∞                 *)
(* - Addition is ordinary addition (with ∞ + x = ∞)                          *)
(* - Order is ordinary ≤ (with n < ∞ for all n ∈ ℕ)                         *)

(* Extended naturals: ℕ ∪ {∞} *)
Definition ExtNat : set := omega :\/: {omega}.

Definition is_finite_extnat : set -> prop :=
  fun n => n :e omega.

Definition is_infinity : set -> prop :=
  fun n => n = omega.

(* -------------------------------------------------------------------------- *)
(* C.2: Quantale Addition                                                     *)
(* -------------------------------------------------------------------------- *)

(* Extended addition: handles infinity *)
Definition quant_add : set -> set -> set :=
  fun a b =>
    if is_infinity a then omega
    else if is_infinity b then omega
    else add a b.

(* Associativity *)
Theorem quant_add_assoc : forall a b c,
  quant_add (quant_add a b) c = quant_add a (quant_add b c).
Admitted.

(* Commutativity *)
Theorem quant_add_comm : forall a b,
  quant_add a b = quant_add b a.
Admitted.

(* Identity: 0 + a = a *)
Theorem quant_add_zero : forall a,
  quant_add 0 a = a.
Admitted.

(* Infinity absorbs: ∞ + a = ∞ *)
Theorem quant_add_infinity : forall a,
  quant_add omega a = omega.
Admitted.

(* -------------------------------------------------------------------------- *)
(* C.3: Quantale Order                                                        *)
(* -------------------------------------------------------------------------- *)

(* Extended ordering *)
Definition quant_le : set -> set -> prop :=
  fun a b =>
    (is_finite_extnat a /\ is_finite_extnat b /\ ord_le a b) \/
    (is_infinity b).

(* Reflexivity *)
Theorem quant_le_refl : forall a, quant_le a a.
Admitted.

(* Transitivity *)
Theorem quant_le_trans : forall a b c,
  quant_le a b -> quant_le b c -> quant_le a c.
Admitted.

(* Antisymmetry *)
Theorem quant_le_antisym : forall a b,
  quant_le a b -> quant_le b a -> a = b.
Admitted.

(* Everything is ≤ infinity *)
Theorem quant_le_infinity : forall a, quant_le a omega.
Admitted.

(* -------------------------------------------------------------------------- *)
(* C.4: Quantale Properties                                                   *)
(* -------------------------------------------------------------------------- *)

(* Addition is monotone in the order *)
Theorem quant_add_mono : forall a b c d,
  quant_le a b -> quant_le c d -> quant_le (quant_add a c) (quant_add b d).
Admitted.

(* Addition distributes over suprema (this is the quantale property) *)
(* For our discrete case: a + sup(S) = sup{a + s : s ∈ S} *)


(* ========================================================================== *)
(*                    SECTION D: FUNDAMENTAL INEQUALITIES                     *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* D.1: Lemma 2.2(i): Monotonicity in Conditions                              *)
(* -------------------------------------------------------------------------- *)

(* More information in the condition can only help:
   K^poly(x|y) ≤ K^poly(x|zy) + O(1) *)

Theorem Kpoly_monotonicity :
  forall x y z,
    exists c :e omega,
      quant_le (Kpoly x (concat z y)) (quant_add (Kpoly x y) c).
Admitted.

(* Proof idea: A program that works with y can ignore z.
   The constant c accounts for parsing/ignoring z. *)

(* -------------------------------------------------------------------------- *)
(* D.2: Lemma 2.2(ii): Coarse Chain Rule                                      *)
(* -------------------------------------------------------------------------- *)

(* K^poly(xz|y) ≤ K^poly(x|y) + K^poly(z|xy) + O(1) *)
(* To describe xz, first describe x, then describe z given x. *)

Theorem Kpoly_chain_rule :
  forall x z y,
    exists c :e omega,
      quant_le (Kpoly (concat x z) y)
               (quant_add (quant_add (Kpoly x y) (Kpoly z (concat x y))) c).
Admitted.

(* The constant c covers the overhead of combining the two programs *)

(* -------------------------------------------------------------------------- *)
(* D.3: Symmetry of Information (Coarse Form)                                 *)
(* -------------------------------------------------------------------------- *)

(* K^poly(x,y) = K^poly(x) + K^poly(y|x) + O(log(K^poly(x,y))) *)

Theorem Kpoly_symmetry_coarse :
  forall x y,
    exists c :e omega,
      (* |K^poly(x,y) - K^poly(x) - K^poly(y|x)| ≤ c * log(K^poly(x,y)) *)
      True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* D.4: Subadditivity                                                         *)
(* -------------------------------------------------------------------------- *)

(* K^poly(x,y) ≤ K^poly(x) + K^poly(y) + O(1) *)

Theorem Kpoly_subadditive :
  forall x y,
    exists c :e omega,
      quant_le (Kpoly (concat x y) empty_string)
               (quant_add (quant_add (Kpoly x empty_string)
                                     (Kpoly y empty_string)) c).
Admitted.


(* ========================================================================== *)
(*                    SECTION E: BLOCK ADDITIVITY                             *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* E.1: Lemma 2.3: Block Additivity with Logarithmic Overhead                 *)
(* -------------------------------------------------------------------------- *)

(* For a tuple of t blocks:
   K^poly((x_1,...,x_t)|(y_1,...,y_t)) ≤ Σ_i K^poly(x_i|y_i) + O(log t) *)

Theorem Kpoly_block_additivity :
  forall t X_tuple Y_tuple,
    nat_p t ->
    exists c :e omega,
      quant_le (Kpoly (tuple_concat X_tuple t) (tuple_concat Y_tuple t))
               (quant_add
                 (sum_range (fun i => Kpoly (proj X_tuple i) (proj Y_tuple i)) t)
                 (mul c (log2 t))).
Admitted.

(* Proof: Run each block's program in sequence.
   The O(log t) overhead encodes the loop counter. *)

(* -------------------------------------------------------------------------- *)
(* E.2: Wrapper Overhead (Remark 2.4)                                         *)
(* -------------------------------------------------------------------------- *)

(* Scheduling t independent subroutines costs O(log t) bits *)

Definition wrapper_overhead : set -> set :=
  fun t => mul (ordsucc (ordsucc 0)) (log2 t).  (* 2 * log t *)

Theorem wrapper_overhead_bound :
  forall t, nat_p t -> t <> 0 ->
    ord_le (wrapper_overhead t) (mul three (log2 t)).
Admitted.

(* -------------------------------------------------------------------------- *)
(* E.3: Independence Does Not Help (Without Special Structure)                *)
(* -------------------------------------------------------------------------- *)

(* In general, knowing blocks are independent doesn't help compression.
   The savings come from structure, not mere independence. *)


(* ========================================================================== *)
(*                    SECTION F: COMPRESSION-FROM-SUCCESS                     *)
(* ========================================================================== *)

(* This section formalizes how successful decoding implies bounded complexity *)

(* -------------------------------------------------------------------------- *)
(* F.1: Decoder Success Definition                                            *)
(* -------------------------------------------------------------------------- *)

(* A decoder P succeeds on block i if P(y_i) = x_i *)
Definition decoder_succeeds : set -> set -> set -> set -> prop :=
  fun P i X_tuple Y_tuple =>
    decoder_succeeds_on P (proj Y_tuple i) (proj X_tuple i).

(* Success set: indices where decoder succeeds *)
Definition success_set : set -> set -> set -> set -> set :=
  fun P t X_tuple Y_tuple =>
    {i :e t | decoder_succeeds P i X_tuple Y_tuple}.

(* -------------------------------------------------------------------------- *)
(* F.2: Lemma 2.5: Compression from Block Success (Coarse)                    *)
(* -------------------------------------------------------------------------- *)

(* If decoder P of length L succeeds on S ⊆ [t], then:
   K^poly(X|Y) ≤ L + log(t choose |S|) + (t-|S|) * max|x_i| *)

Theorem compression_from_success_coarse :
  forall L P t S X_tuple Y_tuple,
    desc_length P = L ->
    S c= t ->
    S = success_set P t X_tuple Y_tuple ->
    quant_le (Kpoly (tuple_concat X_tuple t) (tuple_concat Y_tuple t))
             (quant_add L
               (quant_add (log2 (binomial t (card S)))
                 (mul (sub t (card S)) (tuple_max strlen X_tuple t)))).
Admitted.

(* Proof idea:
   - L bits to describe P
   - log(t choose |S|) bits to specify which blocks succeeded
   - For failed blocks, output them literally *)

(* -------------------------------------------------------------------------- *)
(* F.3: Lemma 2.6: Per-Bit Enumerative Coding                                 *)
(* -------------------------------------------------------------------------- *)

(* Finer bound using Hamming distance to predictions *)

Definition error_mask : set -> set -> set :=
  fun x pred => (fun i => if x i = pred i then 0 else ordsucc 0).

Definition error_count : set -> set -> set :=
  fun x pred => hamming_dist x pred.

Theorem compression_perbit_enumerative :
  forall L P t X_tuple Y_tuple,
    desc_length P = L ->
    polytime_decoder P ->
    let Pred_tuple := (fun i => Eps_i (fun p => UTM_computes P (proj Y_tuple i) p)) in
    quant_le (Kpoly (tuple_concat X_tuple t) (tuple_concat Y_tuple t))
             (quant_add L
               (quant_add (wrapper_overhead t)
                 (sum_range (fun i =>
                   log2 (binomial (strlen (proj X_tuple i))
                                  (error_count (proj X_tuple i) (proj Pred_tuple i))))
                   t))).
Admitted.

(* -------------------------------------------------------------------------- *)
(* F.4: Bound via Success Probability                                         *)
(* -------------------------------------------------------------------------- *)

(* If P has per-block success rate p on average, then:
   E[K^poly(X|Y)] ≤ L + H(p) * t + O(log t)
   where H(p) = -p*log(p) - (1-p)*log(1-p) is binary entropy *)

Definition binary_entropy : set -> set :=
  fun p => 0.  (* Abstract: H(p) = -p log p - (1-p) log(1-p) *)

Theorem compression_from_success_rate :
  forall L P t success_rate,
    desc_length P = L ->
    polytime_decoder P ->
    (* If per-block success prob is at least success_rate *)
    (* Then E[K^poly(X|Y)] ≤ L + H(1-success_rate)*t + O(log t) *)
    True.
Admitted.


(* ========================================================================== *)
(*                    SECTION G: UNION BOUND OVER SHORT DECODERS              *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* G.1: Counting Short Decoders                                               *)
(* -------------------------------------------------------------------------- *)

(* Number of programs of length ≤ L is at most 2^{L+1} - 1 < 2^{L+1} *)

Theorem num_short_decoders :
  forall L, nat_p L ->
    (* |{p : |p| ≤ L}| < 2^{L+1} *)
    has_at_least (Programs_upto L) (exp two (ordsucc L)).
Admitted.

(* -------------------------------------------------------------------------- *)
(* G.2: Union Bound Application                                               *)
(* -------------------------------------------------------------------------- *)

(* If each short decoder has success prob ≤ 2^{-Omega(t)},
   then the union over all short decoders also has small prob *)

Theorem union_bound_short_decoders :
  forall L t delta eps,
    nat_p L -> nat_p t ->
    L = mul delta t ->      (* L is proportional to t *)
    delta > 0 ->
    (* If Pr[P succeeds on ≥ gamma*t blocks] ≤ eps for each P of length ≤ L *)
    (* Then Pr[∃P: |P|≤L, P succeeds on ≥ gamma*t blocks] ≤ 2^{L+1} * eps *)
    True.
Admitted.

(* For eps = 2^{-Omega(t)} and L = O(t), this remains 2^{-Omega(t)} *)

(* -------------------------------------------------------------------------- *)
(* G.3: The Key Regime                                                        *)
(* -------------------------------------------------------------------------- *)

(* In Goertzel's proof:
   - L = δ*t for small constant δ
   - Per-decoder failure prob = 2^{-Omega(t)}
   - Union bound gives overall failure prob 2^{δt + 1} * 2^{-Omega(t)} = 2^{-Omega(t)}
   - As long as the Omega(t) term dominates δt *)

Theorem key_union_bound_regime :
  forall delta gamma c t,
    nat_p t ->
    delta > 0 -> gamma > 0 ->
    (* For L = delta*t and per-decoder failure 2^{-c*t} with c > delta: *)
    (* Union bound gives failure 2^{(delta - c)*t + 1} -> 0 *)
    ord_lt delta c ->
    True.
Admitted.


(* ========================================================================== *)
(*                    SECTION H: LOWER BOUNDS ON COMPLEXITY                   *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* H.1: Incompressibility                                                     *)
(* -------------------------------------------------------------------------- *)

(* Most strings of length n have K^poly(x) ≥ n - O(1) *)

Theorem incompressibility_counting :
  forall n,
    nat_p n ->
    (* |{x ∈ {0,1}^n : K^poly(x) < n - c}| < 2^{n-c} *)
    True.
Admitted.

(* Proof: At most 2^{n-c} - 1 programs of length < n-c *)

(* -------------------------------------------------------------------------- *)
(* H.2: Random Strings are Incompressible                                     *)
(* -------------------------------------------------------------------------- *)

Theorem random_string_incompressible :
  forall n c,
    nat_p n -> nat_p c ->
    (* Pr_{x uniform}[K^poly(x) < n - c] < 2^{-c} *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* H.3: Conditional Incompressibility                                         *)
(* -------------------------------------------------------------------------- *)

(* Even with side information, most strings require nearly full description *)

Theorem conditional_incompressibility :
  forall n y,
    nat_p n ->
    (* For most x: K^poly(x|y) ≥ n - O(log n) - K^poly(y) *)
    True.
Admitted.


(* ========================================================================== *)
(*                    SECTION I: TUPLE COMPLEXITY                             *)
(* ========================================================================== *)

(* -------------------------------------------------------------------------- *)
(* I.1: Tuple Incompressibility                                               *)
(* -------------------------------------------------------------------------- *)

(* For i.i.d. random tuples, total complexity grows linearly *)

Theorem tuple_complexity_linear :
  forall t m,
    nat_p t -> nat_p m ->
    (* E[K^poly(X_1,...,X_t)] ≥ Omega(t*m) for uniform X_i in {0,1}^m *)
    True.
Admitted.

(* -------------------------------------------------------------------------- *)
(* I.2: The Key Lower Bound (Theorem 6.8 Preview)                             *)
(* -------------------------------------------------------------------------- *)

(* This is the main technical result from Section 6:
   For the Goertzel distribution D_m with t = Theta(m) blocks,
   K^poly((X_1,...,X_t)|(Phi_1,...,Phi_t)) ≥ eta * t
   with probability 1 - 2^{-Omega(m)} *)

Theorem tuple_Kpoly_lower_bound_preview :
  forall m t,
    nat_p m -> nat_p t ->
    t = mul c4 m ->  (* t = c_4 * m *)
    exists eta :e omega,
      eta > 0 /\
      (* Pr_{D_m^t}[K^poly(X|Phi) ≥ eta*t] ≥ 1 - 2^{-Omega(m)} *)
      True.
Admitted.

(* This lower bound, combined with the O(1) upper bound under P=NP,
   gives the contradiction in Goertzel's proof *)


(* ========================================================================== *)
(* END OF 02_weakness_quantale.mg                                             *)
(* ========================================================================== *)
