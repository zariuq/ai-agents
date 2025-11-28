(* UNIQUENESS-SPARSIFICATION LEMMA *)
(* Target theorem and proof structure for Crux #2 *)

Variable m : set.
Axiom m_in_omega : m :e omega.
Axiom m_large : 16 c= m.

Definition log_m : set := Eps_i (fun k => k :e omega /\ exp_nat 2 k c= m).
Definition radius : set := mul_nat 3 log_m.

(* ============================================================ *)
(* SECTION 1: IMPORT FROM AXIOMS                                *)
(* ============================================================ *)

(* Chart probability definitions *)
Definition Pr_uncond_chart : set -> set -> set := fun C i =>
  Eps_i (fun p => p :e omega).

Definition Pr_Dm_chart : set -> set -> set := fun C i =>
  Eps_i (fun p => p :e omega).

Definition Pr_Unq : set := Eps_i (fun p => p :e omega /\ 1 c= mul_nat p m).

Definition Pr_Unq_given_C : set -> set -> set := fun C i =>
  Eps_i (fun p => p :e omega).

(* From axioms: unconditioned chart bound *)
Definition uncond_bound_constant : set := 3.

Axiom uncond_chart_bound : forall C i : set,
  i :e m ->
  mul_nat (Pr_uncond_chart C i) (exp_nat m uncond_bound_constant) c= 1.

(* From axioms: VV probability *)
Axiom VV_bound : 1 c= mul_nat Pr_Unq m.

(* ============================================================ *)
(* SECTION 2: THE TARGET THEOREM                                *)
(* ============================================================ *)

(*
   UNIQUENESS-CONDITIONING STABILITY LEMMA (TARGET)

   For any fixed radius-r chart C and any variable i ∈ [m]:

     Pr_{(Φ,i) ~ D_m}[(Φ,i) matches C] ≤ poly(m) · Pr_{uncond}[(Φ,i) matches C]

   Equivalently:
     Pr[Unq | C] ≤ poly(m) · Pr[Unq]

   In particular, the m^{-Ω(1)} bounds for chart probability survive
   conditioning on Unq(Φ).
*)

Definition poly_factor : set := mul_nat m m.

Definition uniqueness_conditioning_stability : prop :=
  forall C i : set,
    i :e m ->
    Pr_Dm_chart C i c= mul_nat poly_factor (Pr_uncond_chart C i).

(* Equivalent via Bayes *)
Definition uniqueness_robustness : prop :=
  forall C i : set,
    i :e m ->
    Pr_Unq_given_C C i c= mul_nat poly_factor Pr_Unq.

(* ============================================================ *)
(* SECTION 3: PROOF STRUCTURE                                   *)
(* ============================================================ *)

(*
   PROOF SKETCH:

   By Bayes' rule:
     Pr[C | Unq] / Pr[C] = Pr[Unq | C] / Pr[Unq]

   So the target is equivalent to:
     Pr[Unq | C] ≤ poly(m) · Pr[Unq]

   FACTORIZATION:

   Let C = (C_F, a_i, b) where:
   - C_F = F-local structure at position i
   - a_i = column i of matrix A
   - b = RHS vector

   Pr[Unq | C] = Pr[Unq | C_F, a_i, b]

   KEY OBSERVATIONS:

   1. |S(F,h)| depends on (F, h) only, not on (A, b)
   2. Given |S| = k, Unq happens iff exactly 1 of k solutions has Ax = b
   3. This depends on A-minus-column-i and (a_i, b)
   4. A-minus-column-i is STILL RANDOM given C (since C only fixes a_i)

   DECOMPOSITION:

   Pr[Unq | C] = Σ_k Pr[Unq | C, |S|=k] · Pr[|S|=k | C]
*)

(* Step 1: Factor S-size from F-structure *)
Definition S_size_given_C : set -> set -> set := fun C k =>
  Eps_i (fun p => p :e omega).

(* Step 2: Unq probability given |S|=k and C *)
Definition Unq_given_S_size : set -> set -> set -> set := fun C i k =>
  Eps_i (fun p => p :e omega).

(* Step 3: Sum decomposition *)
Definition Pr_Unq_given_C_decomposed : set -> set -> set := fun C i =>
  Eps_i (fun p => p :e omega).

(* ============================================================ *)
(* SECTION 4: THE KEY INDEPENDENCE CLAIMS                       *)
(* ============================================================ *)

(*
   CLAIM 1: Pr[|S|=k | C] ≤ poly(m) · Pr[|S|=k | C_F]

   Intuition: (a_i, b) are independent of F, so they don't bias |S|.

   More precisely:
   - |S(F,h)| depends only on (F, h)
   - C_F tells us about (F, h) locally
   - (a_i, b) are uniform random, independent of (F, h)
   - So Pr[|S|=k | C] = Pr[|S|=k | C_F] exactly (not just approximately)
*)

Definition claim_1_VV_independent : prop :=
  forall C_F ai b k : set,
    k :e omega ->
    True.

Axiom VV_independent_of_S : claim_1_VV_independent.

(*
   CLAIM 2: Pr[|S|=k | C_F] ≤ poly(m) · Pr[|S|=k]

   This is the LOCAL-GLOBAL DECORRELATION claim.

   Intuition:
   - C_F involves O(m^ε) variables (radius r = O(log m))
   - |S| is a global property depending on all m variables
   - For random 3-CNF, local patterns should be nearly independent of global |S|

   This is the CRUX of Crux #2.
*)

Definition claim_2_local_global : prop :=
  forall C_F k : set,
    k :e omega ->
    True.

(* THIS IS THE KEY AXIOM THAT NEEDS PROOF *)
Axiom local_global_decorrelation : claim_2_local_global.

(*
   CLAIM 3: Pr[Unq | C, |S|=k] ≤ poly(m) · Pr[Unq | |S|=k]

   Given |S| = k, Unq depends on:
   - Which k solutions are selected (determined by F)
   - Which one has Ax = b (random over A, b)

   The (a_i, b) part of C fixes SOME linear constraints, but:
   - A-minus-column-i is still random
   - The analysis is similar to standard VV with one column fixed

   Need to show fixing one column doesn't change Unq probability much.
*)

Definition claim_3_VV_analysis : prop :=
  forall C k : set,
    k :e omega ->
    Unq_given_S_size C 0 k c= mul_nat m (Unq_given_S_size Empty 0 k).

Axiom VV_one_column_fixed : claim_3_VV_analysis.

(* ============================================================ *)
(* SECTION 5: COMBINING THE CLAIMS                              *)
(* ============================================================ *)

Theorem uniqueness_stability_from_claims :
  claim_1_VV_independent ->
  claim_2_local_global ->
  claim_3_VV_analysis ->
  uniqueness_robustness.
Admitted.

(* ============================================================ *)
(* SECTION 6: WHAT CLAIM 2 REALLY NEEDS                         *)
(* ============================================================ *)

(*
   CLAIM 2 IN DETAIL:

   For random 3-CNF F at density α, mask h, variable i, radius r:

   Pr[|S(F,h)| = k | F-local pattern at i is C_F] ≤ poly(m) · Pr[|S| = k]

   WHY THIS SHOULD BE TRUE:

   1. EXPANSION PROPERTY:
      Random 3-CNF is a good expander with high probability.
      Local structure has bounded influence on global satisfiability.

   2. SOLUTION GEOMETRY:
      At high density, solutions (if any) are scattered.
      Local constraints don't determine global count.

   3. TYPICALITY:
      Most F have "typical" solution counts given their local structure.
      Atypical F (with unusual |S|) are rare for any fixed C_F.

   WHY THIS MIGHT BE FALSE:

   1. NEAR-CRITICAL DENSITY:
      At density close to satisfiability threshold, local patterns
      might strongly predict satisfiability.

   2. BOTTLENECK STRUCTURES:
      Certain local patterns might "force" near-uniqueness by
      creating propagation bottlenecks.

   3. LONG-RANGE CORRELATIONS:
      Random 3-SAT has non-trivial long-range correlations that
      might couple local and global structure.
*)

(* Formalization of expansion property *)
Definition expansion_implies_independence : prop :=
  forall C_F k : set,
    k :e omega ->
    True.

(* Formalization of typicality *)
Definition typical_F_bound : prop :=
  forall C_F : set,
    True.

(* ============================================================ *)
(* SECTION 7: THE EXPERIMENTAL TEST                             *)
(* ============================================================ *)

(*
   EXPERIMENT SPECIFICATION:

   For m = 10, 15, 20, 25, 30:

   1. Sample N = 10000 formulas F from random 3-CNF
   2. Sample mask h uniformly
   3. Compute |S(F,h)| by brute force (feasible for m ≤ 30)
   4. For formulas with |S| > 0:
      a. Sample A, b from VV distribution
      b. Check if Unq holds (exactly one solution with Ax = b)
      c. For Unq instances: record local chart C_i for random i
   5. Build histogram of charts for:
      - Unconditioned distribution
      - Unq-conditioned distribution (D_m)
   6. Compute ratio Pr_Dm[C] / Pr_uncond[C] for each observed chart

   SUCCESS CRITERION:
   - All ratios ≤ m^4 for observed charts
   - Ratio doesn't grow faster than poly(m) as m increases
*)

Definition experimental_success : prop :=
  forall C i : set,
    i :e m ->
    Pr_Dm_chart C i c= mul_nat (exp_nat m 4) (Pr_uncond_chart C i).

(* ============================================================ *)
(* SECTION 8: CONSEQUENCE FOR SPARSIFICATION                    *)
(* ============================================================ *)

(*
   IF uniqueness_conditioning_stability HOLDS:

   The sparsification bounds from unconditioned analysis transfer to D_m.

   Specifically, from uncond_chart_bound:
     Pr_uncond[C] ≤ m^{-k} for some k > 0

   Combined with uniqueness_conditioning_stability:
     Pr_Dm[C] ≤ poly(m) · Pr_uncond[C] ≤ poly(m) · m^{-k} = m^{-k'}

   For k' = k - O(1) > 0, sparsification STILL WORKS under D_m.
*)

Definition sparsification_under_Dm : prop :=
  forall C i : set,
    i :e m ->
    mul_nat (Pr_Dm_chart C i) (exp_nat m 2) c= 1.

Theorem sparsification_from_stability :
  uniqueness_conditioning_stability ->
  sparsification_under_Dm.
Admitted.

(* ============================================================ *)
(* SECTION 9: FINAL TARGET THEOREM                              *)
(* ============================================================ *)

Definition crux2_target_theorem : prop :=
  uniqueness_conditioning_stability /\
  sparsification_under_Dm.

Theorem CRUX2_SPARSIFICATION_UNDER_UNIQUENESS :
  claim_1_VV_independent ->
  claim_2_local_global ->
  claim_3_VV_analysis ->
  crux2_target_theorem.
Admitted.

(* ============================================================ *)
(* SECTION 10: STATUS AND NEXT STEPS                            *)
(* ============================================================ *)

(*
   CRUX #2 STATUS:

   GIVEN (from paper / standard):
   - Claim 1: VV layer independent of F ✓ (by construction)
   - Claim 3: VV analysis with one column fixed ✓ (standard VV argument)

   NEEDS PROOF OR COUNTEREXAMPLE:
   - Claim 2: Local-global decorrelation for random 3-CNF

   RECOMMENDED APPROACH:

   1. THEORETICAL: Prove Claim 2 using:
      - Expansion properties of random 3-SAT
      - Cavity method or replica symmetric analysis
      - Or: find a simpler direct argument

   2. EXPERIMENTAL: Test Claim 2 for small m:
      - Sample from both distributions
      - Compare chart frequencies
      - Look for counterexamples

   If Claim 2 holds: CRUX #2 RESOLVED, sparsification under D_m follows
   If Claim 2 fails: CRUX #2 is a REAL GAP in the proof
*)

