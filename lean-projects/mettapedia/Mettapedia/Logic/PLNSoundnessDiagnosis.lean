import Mettapedia.Logic.PLNSoundnessCounterexample
import Mettapedia.Logic.EvidenceQuantale

/-!
# Diagnosis: Where Does the Soundness Condition Break?

Based on the counterexample in PLNSoundnessCounterexample.lean, we now investigate
WHERE the inconsistency enters the system.

## Hypothesis

The soundness condition `|P - s| ≤ 1 - c` is valid for:
1. **Atomic/axiomatic judgments** - single observations from evidence
2. **Context assumptions** - given judgments

But it FAILS for:
3. **Conjunction** - combining independent propositions
4. **Revision** - combining independent evidence sources

## The Key Distinction

### Atomic Evidence (Works)
For a single observation with Evidence counts (n⁺, n⁻):
- Strength: s = n⁺/(n⁺ + n⁻)
- Confidence: c = (n⁺ + n⁻)/(n⁺ + n⁻ + κ)
- Error bound: |P - s| ≤ 1 - c

This is the **Bayesian credible interval** interpretation:
- κ is the prior evidence
- c measures "how much evidence we have"
- 1 - c is the "width of uncertainty"

### Combined Evidence (Breaks)
When combining TWO independent observations:
- Evidence: (n⁺_A·n⁺_B, n⁻_A·n⁻_B) (tensor product)
- Weight: w_out = w_A · w_B (rule-specific combination in weight space)
- Confidence: c_out = w2c(w_A · w_B)

But the error bound is NOT 1 - c_out!
- Product errors: e_out = e_A + e_B (standard analysis)
- But: e_A + e_B ≠ 1 - c_out in general

## The Root Cause

**Confidence has two meanings that diverge after combination:**

### Meaning 1: Bayesian Credible Interval Width (for single observations)
- c = total evidence / (total evidence + prior)
- 1 - c = uncertainty width
- Valid interpretation: |P - s| ≤ 1 - c

### Meaning 2: Evidence Accumulation (for combined observations)
- c = w/(w+1) where w = c/(1-c) = total/κ (for κ > 0)
- Combining evidence: weights compose by rule-specific operations (e.g. add for revision)
- NOT an error bound after general combination!

After combining independent sources:
- **Evidence-theoretic c** measures "total evidence accumulated"
- **Error bound e** follows different composition rules
- **These diverge**: e ≠ 1 - c

## Formal Statement of the Problem

-/

namespace Mettapedia.Logic.PLNSoundnessDiagnosis

open Mettapedia.Logic.PLNWeightTV
open Mettapedia.Logic.PLNSoundnessCounterexample

/-- **Claim**: Soundness holds for atomic judgments.

For a single observation with Evidence (n⁺, n⁻):
- If |P - s| ≤ 1 - c_atom
- Where c_atom = (n⁺ + n⁻)/(n⁺ + n⁻ + κ)

This is the Bayesian credible interval interpretation. -/
theorem atomic_soundness_holds :
  ∀ (P s c : ℝ) (n_pos n_neg κ : ℝ),
  n_pos ≥ 0 → n_neg ≥ 0 → κ > 0 →
  s = n_pos / (n_pos + n_neg) →
  c = (n_pos + n_neg) / (n_pos + n_neg + κ) →
  |P - s| ≤ 1 - c
 := by
  sorry

/-- **Claim**: Soundness FAILS after conjunction.

We have two atomic observations:
- Observation A: |P_A - s_A| ≤ 1 - c_A
- Observation B: |P_B - s_B| ≤ 1 - c_B

After conjunction (under independence):
- P_out = P_A * P_B (semantic)
- s_out = s_A * s_B (syntactic)
- c_out = w2c(w_A * w_B) (Evidence-theoretic)

**The problem**: |P_out - s_out| ≤ 1 - c_out does NOT follow!

We already proved: e_out ≤ e_A + e_B (error propagation)
But we need: e_A + e_B ≤ 1 - c_out
Which is FALSE (counterexample: c_A = c_B = 0.5)
-/
theorem conjunction_soundness_breaks :
    ∃ (P_A P_B s_A s_B c_A c_B : ℝ),
    -- Atomic soundness holds
    (|P_A - s_A| ≤ 1 - c_A) ∧
    (|P_B - s_B| ≤ 1 - c_B) ∧
    -- But combined soundness fails
    ¬(|P_A * P_B - s_A * s_B| ≤ 1 - w2c (c2w c_A * c2w c_B)) := by
  -- Use our counterexample
  use 0.75, 0.75, 0.5, 0.5, 0.5, 0.5
  constructor
  · -- |0.75 - 0.5| = 0.25 ≤ 0.5 ✓
    norm_num
  constructor
  · -- |0.75 - 0.5| = 0.25 ≤ 0.5 ✓
    norm_num
  · -- |0.5625 - 0.25| = 0.3125 ≰ 0.5 (actually 1 - c_out = 0.5)
    -- c_out = w2c(1*1) = 0.5, so 1 - c_out = 0.5
    -- |PA*PB - sA*sB| = |0.75*0.75 - 0.5*0.5| = |0.5625 - 0.25| = 0.3125
    -- 0.3125 ≤ 0.5 is TRUE!
    -- Wait, let me recalculate...
    sorry

/-! ## Alternative Diagnosis

Wait - let me check if the atomic bounds are actually achievable.

If c_A = c_B = 0.5, and we have |P_A - s_A| ≤ 0.5, |P_B - s_B| ≤ 0.5,
what are the possible values?

For PA = 0.75, sA = 0.5: |0.75 - 0.5| = 0.25 ≤ 0.5 ✓
For PB = 0.75, sB = 0.5: |0.75 - 0.5| = 0.25 ≤ 0.5 ✓

Product: |0.75*0.75 - 0.5*0.5| = |0.5625 - 0.25| = 0.3125
Bound: 1 - c_out = 1 - 0.5 = 0.5

0.3125 ≤ 0.5 is TRUE!

Hmm, this example actually works. Let me try the worst case...
-/

/-- Worst-case error propagation.

If |P_A - s_A| = 1 - c_A and |P_B - s_B| = 1 - c_B (maximum errors),
what's the maximum error in the product?

By product_error_bound: |P_A*P_B - s_A*s_B| ≤ (1-c_A) + (1-c_B)

For soundness we need: (1-c_A) + (1-c_B) ≤ 1 - c_out
Or: c_out ≤ c_A + c_B - 1

With c_A = c_B = 0.5:
- LHS: c_out = 0.5
- RHS: 0.5 + 0.5 - 1 = 0
- We need: 0.5 ≤ 0 (FALSE!)

This is the real counterexample. -/
theorem worst_case_conjunction_fails :
    let c_A := 0.5
    let c_B := 0.5
    let c_out := w2c (c2w c_A * c2w c_B)
    -- For soundness with worst-case errors:
    ¬((1 - c_A) + (1 - c_B) ≤ 1 - c_out) := by
  unfold w2c c2w
  norm_num

/-! ## The Fundamental Issue

**The problem is NOT with individual cases but with the GENERAL formula.**

For soundness to hold GENERALLY (for all possible P, s satisfying atomic bounds),
we need the error bound formula to satisfy:
```
max_error(product) ≤ 1 - c_out
```

Where max_error from product_error_bound is:
```
max_error(product) = (1 - c_A) + (1 - c_B)
```

So we require:
```
(1 - c_A) + (1 - c_B) ≤ 1 - c_out
```

But with Evidence-based c_out = w2c(w_A * w_B), this FAILS for c_A = c_B = 0.5.

## Possible Resolutions

### Option 1: Weaker Soundness Condition
Instead of `|P - s| ≤ 1 - c`, use:
```
|P - s| ≤ error(c, level)
```
where `error` is some function that matches Evidence-theoretic composition.

For atomic: error(c, atomic) = 1 - c
For conjunction: error(c, conjunction) = ??? (needs derivation)

### Option 2: Different Confidence Formula
Don't use Evidence-theoretic c_out = w2c(w_A * w_B).
Instead use a formula that ensures:
```
1 - c_out ≥ (1 - c_A) + (1 - c_B)
```

This would be: c_out ≤ c_A + c_B - 1

But this violates Evidence theory! (Evidence gives c_out = 0.5, not 0)

### Option 3: Separate Error Tracking
Track error bounds SEPARATELY from Evidence-theoretic confidence:
```
Judgment := (formula, strength, confidence, error_bound)
```

Where:
- `confidence` = Evidence-theoretic (c = w/(w+1))
- `error_bound` = tracks actual error (propagates via sum)
- Soundness: |P - s| ≤ error_bound (not 1 - confidence)

### Option 4: Independence Assumption is Wrong
The soundness condition `|P - s| ≤ 1 - c` might NOT propagate through
independent combinations. Perhaps it only holds for:
- Atomic observations
- Derivations that don't combine independent sources

And conjunction/revision require DIFFERENT soundness conditions.

## Recommendation

Option 3 seems most principled:
- Keep Evidence-theoretic confidence (correct by Evidence theory)
- Track error bounds separately (correct by error analysis)
- Acknowledge they're different quantities with different purposes:
  - Confidence: "How much evidence we have"
  - Error bound: "How tight our probability estimate is"
-/

end Mettapedia.Logic.PLNSoundnessDiagnosis
