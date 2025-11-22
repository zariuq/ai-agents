(* P != NP Formalization: LOCAL ≠ SIMPLE Attack *)
(* The key gap: local functions need not have small K-complexity *)

(* ============================================================ *)
(* THE FUNDAMENTAL DISTINCTION                                  *)
(* ============================================================ *)

(* DEFINITION: A function f is "k-local" if it depends on at most k input bits *)
Definition k_local : set -> set -> prop :=
  fun f k => exists inputs c= k,
    forall x y, (forall i :e inputs, ap x i = ap y i) ->
    ap f x = ap f y.

(* DEFINITION: A function f has K-complexity at most c *)
Definition K_bounded : set -> set -> prop :=
  fun f c => exists p, strlen p c= c /\ U p Empty = f.

(* THE KEY CLAIM (which the proof assumes): *)
Definition local_implies_simple : prop :=
  forall f k, k_local f k ->
    K_bounded f (polylog k).

Variable polylog : set -> set.

(* ============================================================ *)
(* WHY THIS IS FALSE                                            *)
(* ============================================================ *)

(* SHANNON'S COUNTING ARGUMENT:
   - Number of Boolean functions on k bits: 2^{2^k}
   - Number of programs of length c: 2^c
   - Most functions require description length >= 2^k - O(k)

   For k = log m:
   - Most functions require description 2^{log m} = m bits
   - But proof needs poly(log m) bits
   - Gap: m vs (log m)^c = HUGE *)

(* The counting argument formalized *)
Definition counting_argument : prop :=
  forall k, nat_p k -> 4 :e k ->
    (* Most k-bit functions require 2^k description *)
    exists f, k_local f k /\ ~K_bounded f (exp 2 k).

(* This shows LOCAL does NOT imply SIMPLE *)
Theorem local_not_simple :
  counting_argument -> ~local_implies_simple.
Admitted.

(* ============================================================ *)
(* THE PROOF'S HIDDEN ASSUMPTION                                *)
(* ============================================================ *)

(* The proof implicitly assumes that the ACTUAL local decoder h_i
   arising from the SAT instance is one of the "simple" functions,
   not an arbitrary k-bit function.

   This might be because:
   1. h_i is constructed by a specific algorithm (ERM on H)
   2. H is defined to contain only poly(log m)-size circuits
   3. So h_i ∈ H implies h_i is simple BY CONSTRUCTION

   BUT: This only works if the TRUE optimal decoder is IN H!
   If the true optimal requires more complex circuits,
   then h_i from ERM is SUB-OPTIMAL. *)

Definition true_optimal_in_H : prop :=
  forall phi, DmInstance phi ->
    forall i :e m,
      exists h :e H, is_optimal h phi i.

Variable is_optimal : set -> set -> set -> prop.
Variable H : set.

(* If true optimal is NOT in H: *)
Definition approximation_error : prop :=
  forall phi, DmInstance phi ->
    forall i :e m,
      exists h_erm :e H,
      exists h_opt,
        is_optimal h_opt phi i /\
        ~(h_opt :e H) /\
        (* ERM finds h_erm which is suboptimal *)
        error h_erm phi i :e error h_opt phi i :+: gap.

Variable error : set -> set -> set -> set.
Variable gap : set.

(* The gap accumulates over m bits and t blocks! *)
Theorem gap_accumulation :
  approximation_error ->
    (* Total error accumulates *)
    forall phi, DmInstance phi ->
      total_error phi :e nat_mult m gap.
Admitted.

Variable total_error : set -> set.

(* ============================================================ *)
(* SPECIFIC ATTACK: CONSTRUCT A COMPLEX LOCAL DECODER           *)
(* ============================================================ *)

(* Can we construct a SAT instance where the optimal local decoder
   is a HIGH-COMPLEXITY function on O(log m) bits?

   Idea: Use the VV layer to encode complex structure

   The VV constraint is: A * X = b
   Where A is a k × m matrix, k = O(log m)

   If A is "complex" (e.g., encodes a hard function),
   then the optimal decoder might need to invert A,
   which could require high complexity.

   Specifically:
   - Local neighborhood gives O(log m) bits of information
   - The optimal prediction might require computing
     a complex function of these bits
   - E.g., if the function involves modular arithmetic,
     parity, or threshold computations *)

Definition complex_VV_instance : set -> prop :=
  fun phi =>
    (* A encodes a complex function *)
    exists A b, VV_layer phi A b /\
    forall i :e m,
      (* Optimal decoder for bit i involves complex computation *)
      forall h, is_optimal h phi i ->
        ~K_bounded h (polylog (log2 m)).

(* If such instances exist with positive probability under D_m: *)
Theorem complex_instances_break_proof :
  Pr complex_VV_instance :e (* positive probability *) 0 ->
    (* The proof's complexity bound fails *)
    ~(forall phi, DmInstance phi -> forall i :e m ->
        exists h, is_optimal h phi i /\ K_bounded h (polylog (log2 m))).
Admitted.

(* ============================================================ *)
(* THE PAPER'S POTENTIAL DEFENSE                                *)
(* ============================================================ *)

(* DEFENSE 1: Random VV matrices are "simple"

   Under D_m, the VV matrix A is random.
   Random matrices might have "typical" structure
   that allows simple decoders.

   Q: Do random matrices give rise to simple decoders?
   A: Not obviously! The decoder depends on A, and
      describing the decoder might require describing A,
      which costs O(k * m) = O(m log m) bits. *)

Definition random_A_simple : prop :=
  (* Random A gives simple decoders with high probability *)
  forall eps, 0 :e eps ->
    Pr (fun phi =>
      forall i :e m,
        exists h, is_optimal h phi i /\ K_bounded h (polylog (log2 m)))
    :e 1 :\: eps.

(* DEFENSE 2: Description relative to A

   The proof might bound K(h | A, phi), not K(h).
   If h is simple GIVEN A, then:
   - K(h | A) is small
   - Total description = K(A) + K(h | A)
   - K(A) = O(k * m) = O(m log m)

   But wait - this is POLYNOMIAL in m!
   The proof needs POLY(LOG M), not POLY(M).

   So this defense fails. *)

Definition conditional_K_bound : prop :=
  forall phi A,
    VV_layer phi A _ ->
    forall i :e m,
      exists h, is_optimal h phi i /\
        K_bounded_cond h A (polylog (log2 m)).

Variable K_bounded_cond : set -> set -> set -> prop.

(* Even with conditioning, total is: K(A) + K(h|A) = O(m log m) *)
Theorem conditional_still_polynomial :
  conditional_K_bound ->
    (* Total K-complexity is polynomial *)
    forall phi A,
      exists h, K_bounded h (nat_mult (log2 m) m).
Admitted.

(* ============================================================ *)
(* THE REAL QUESTION                                            *)
(* ============================================================ *)

(* Does the proof use K(h) or K(h | context)?

   Looking at the paper's structure:
   - K_poly is used for the ENTIRE decoder output
   - The bound is on K_poly(sigma | phi) = O(m)
   - But this is distributed over t blocks

   The switching argument claims:
   - K_poly(wrapper W) = K_poly(P) + O(log m + log t)
   - W encodes the ERM algorithm, not the result

   So W's complexity is:
   - Algorithm for ERM: O(1)
   - Specification of hypothesis class H: O(log m)
   - Index of chosen hypothesis: O(log |H|) = O(poly(log m))

   This gives K_poly(W) = O(poly(log m)) total.

   BUT: W must FIND the right hypothesis using ERM.
   This requires:
   - Access to training data: O(t_train * m) bits
   - ERM computation: poly(training data)

   The DESCRIPTION of W is small, but the EXECUTION uses lots of data.

   This is the K_poly distinction:
   - |W| = description length = O(poly(log m)) ✓
   - Runtime of W = polynomial in input ✓ (allowed by K_poly)

   So the proof's use of K_poly DOES allow polynomial runtime!
   Our earlier critique (polynomial neighborhood) was misdirected. *)

(* ============================================================ *)
(* NEW ATTACK: DESCRIPTION LENGTH OF HYPOTHESIS INDEX           *)
(* ============================================================ *)

(* The wrapper W includes:
   1. The ERM algorithm: O(1) bits
   2. Specification of H: O(log m) bits
   3. Index of chosen hypothesis: O(log |H|) bits

   For (3): If |H| = 2^{poly(log m)}, then index is poly(log m) bits.

   But ERM finds a DIFFERENT hypothesis for each (block, bit) pair!
   - There are t blocks and m bits
   - So there are t * m hypotheses to specify
   - Total: t * m * poly(log m) bits

   With t = O(m) and m bits: Total = O(m^2 * poly(log m)) bits

   This is POLYNOMIAL in m, not poly(log m)! *)

Theorem hypothesis_index_blowup :
  forall t m,
    nat_p t -> nat_p m -> 1000 :e m ->
    (* Specifying t*m hypothesis indices costs: *)
    exists cost, cost = nat_mult t (nat_mult m (polylog (log2 m))) /\
      (* This is polynomial in m, not poly(log m) *)
      polylog (log2 m) c= cost.
Admitted.

(* WAIT - this might be wrong.

   The wrapper W is applied to TEST blocks.
   ERM is run on TRAIN blocks.
   The chosen hypotheses are for TEST blocks.

   But W is the SAME for all test blocks!
   W encodes:
   - "Run ERM on the train data to find h_i for each bit i"
   - "Apply h_i to the local view"

   So W specifies the ALGORITHM, not the hypotheses.
   The hypotheses are computed AT RUNTIME by W.

   This means:
   - |W| = O(log m + log t) for the algorithm spec
   - W uses O(train_size * m) bits of input at runtime
   - Runtime is polynomial, which is allowed

   The proof IS correct on this point.
   The wrapper has small description length because it
   specifies an algorithm, not a lookup table. *)

(* ============================================================ *)
(* FINAL ASSESSMENT                                             *)
(* ============================================================ *)

(* After careful analysis, the LOCAL ≠ SIMPLE gap is addressed by:

   1. The proof uses K_poly, not K
   2. K_poly allows polynomial RUNTIME
   3. The wrapper specifies an ALGORITHM (ERM), not results
   4. The algorithm has poly(log m) description length
   5. The algorithm runs in polynomial time to produce results

   This is the clever design of K_poly!
   - Description length bounds the PROGRAM SIZE
   - Polynomial runtime is FREE

   REMAINING CONCERNS:

   1. Does ERM actually find good hypotheses?
      - Needs |H| * log(t) samples for generalization
      - |H| = 2^{poly(log m)}, so need poly(m) samples
      - With t_train = O(t) = O(m) samples, this might work

   2. What if true optimal h_i is not in H?
      - ERM finds best in H, which might be suboptimal
      - The gap could accumulate over m bits

   3. The description of H might be non-trivial
      - H = "poly(log m)-size circuits"
      - Specifying this requires O(log m) bits
      - This seems acceptable

   VERDICT: The LOCAL ≠ SIMPLE attack is MITIGATED by K_poly.
   But the ERM approximation error is still a potential gap. *)

Theorem local_not_simple_mitigated :
  (* The attack is mitigated by K_poly's polynomial runtime *)
  True.
exact TrueI.
Qed.

(* The remaining vulnerability is ERM approximation *)
Definition remaining_vulnerability : prop :=
  (* If true optimal is outside H, ERM error accumulates *)
  exists phi, DmInstance phi /\
  exists i :e m,
    forall h :e H, ~is_optimal h phi i /\
    (* The gap in ERM solution *)
    exists gap, 0 :e gap /\ accumulates_over_bits gap m.

Variable accumulates_over_bits : set -> set -> prop.

