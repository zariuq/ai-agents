import Mathlib.Tactic
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNInferenceRules

namespace Mettapedia.Logic.PLNMettaTruthFunctions

open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNDeduction
open Mettapedia.Logic.PLNInferenceRules

/-!
# PLN Truth Functions (MeTTa / PeTTa `lib_pln.metta`)

This file mirrors the *numerical* truth-value formulas used in the MeTTa PLN library
(`hyperon/PeTTa/lib/lib_pln.metta`).

Design:
- We keep this file purely about formulas and small algebraic facts.
- We do **not** encode any "missing branch" behavior as `empty`; instead we use `Option`.
- Derivations from probability / Evidence live in separate modules.
-/

/-! ## Simple Truth Values -/

/-- A lightweight (strength, confidence) pair.

This intentionally does not enforce bounds `[0,1]`; those are hypotheses in theorems. -/
structure TV where
  s : ℝ
  c : ℝ

namespace TV

@[simp] theorem eta (t : TV) : TV.mk t.s t.c = t := by
  cases t
  rfl

end TV

/-! ## Utility: confidence ↔ weight -/

/-!
We treat MeTTa confidences as lying in `[0,1]`, but the raw library may occasionally hand us
out-of-range values (e.g. `c = 1` leading to division by zero). For νPLN / Evidence semantics,
we interpret confidence via the standard weight transform `w = c/(1-c)` with a hard cap
`MAX_CONF < 1` and a floor at `0`.
-/

def MAX_CONF : ℝ := 0.9999

/-- Clamp an arbitrary real into the confidence range `[0, MAX_CONF]`. -/
def capConf (c : ℝ) : ℝ :=
  max 0 (min c MAX_CONF)

theorem capConf_nonneg (c : ℝ) : 0 ≤ capConf c := by
  simp [capConf]

theorem capConf_lt_one (c : ℝ) : capConf c < 1 := by
  have hmax : MAX_CONF < 1 := by
    unfold MAX_CONF
    norm_num
  have hmin : min c MAX_CONF ≤ MAX_CONF := min_le_right c MAX_CONF
  have hle : capConf c ≤ MAX_CONF := by
    -- `max 0 (min c MAX_CONF) ≤ max 0 MAX_CONF = MAX_CONF` since `0 ≤ MAX_CONF`.
    have h : max 0 (min c MAX_CONF) ≤ max 0 MAX_CONF := max_le_max_left 0 hmin
    have hMAX0 : (0 : ℝ) ≤ MAX_CONF := by
      unfold MAX_CONF
      norm_num
    have hMAX : max 0 MAX_CONF = MAX_CONF := max_eq_right hMAX0
    simpa [capConf, hMAX] using h
  exact lt_of_le_of_lt hle hmax

noncomputable def c2w (c : ℝ) : ℝ :=
  let cc := capConf c
  cc / (1 - cc)

noncomputable def w2c (w : ℝ) : ℝ :=
  let ww := max 0 w
  ww / (ww + 1)

/-! ## PLN Book Formulas (as in `lib_pln.metta`) -/

/-- A Lean helper mirroring MeTTa's `/safe`:
returns `0` when the denominator is `≤ 0`. -/
noncomputable def safeDiv (a b : ℝ) : ℝ :=
  if 0 < b then a / b else 0

/-- `Truth_Deduction` (PLN book, and `lib_pln.metta`).

Inputs:
- `p`, `q`, `r`: term truth values (only the strengths are used as term probabilities)
- `pq`, `qr`: link truth values

Output confidence is the minimum of all input confidences (as in the MeTTa code). -/
noncomputable def truthDeduction (p q r pq qr : TV) : TV :=
by
  classical
  exact
    if conditionalProbabilityConsistency p.s q.s pq.s ∧
       conditionalProbabilityConsistency q.s r.s qr.s then
      let s :=
        if 0.9999 < q.s then
          r.s
        else
          pq.s * qr.s + (1 - pq.s) * (r.s - q.s * qr.s) / (1 - q.s)
      let c := min p.c (min q.c (min r.c (min pq.c qr.c)))
      ⟨s, c⟩
    else
      ⟨1, 0⟩

/-- `Truth_Induction` (PLN book Appendix A, and `lib_pln.metta`).

This is Bayes-inversion on the first premise followed by deduction. -/
noncomputable def truthInduction (a b c ba bc : TV) : TV :=
  -- Naming matches MeTTa:
  -- `a` = A, `b` = B, `c` = C, and links `ba : B→A`, `bc : B→C`.
  let s := plnInductionStrength ba.s bc.s a.s b.s c.s
  -- Fixed: convert confidences to weights before taking `min`, then map back.
  let conf := w2c (min (c2w ba.c) (c2w bc.c))
  ⟨s, conf⟩

/-- `Truth_Abduction` (PLN book Appendix A, and `lib_pln.metta`). -/
noncomputable def truthAbduction (a b c ab cb : TV) : TV :=
  -- Links: `ab : A→B`, `cb : C→B`.
  let s := plnAbductionStrength ab.s cb.s a.s b.s c.s
  let conf := w2c (min (c2w ab.c) (c2w cb.c))
  ⟨s, conf⟩

/-! ### SourceRule / SinkRule aliases

These names emphasize the *shape* of the inference pattern:
- SourceRule: cospan completion `B → A, B → C ⊢ A → C`
- SinkRule:   span completion  `A → B, C → B ⊢ A → C`
-/

/-- SourceRule (cospan completion): alias of `truthInduction`. -/
noncomputable abbrev truthSourceRule := truthInduction

/-- SinkRule (span completion): alias of `truthAbduction`. -/
noncomputable abbrev truthSinkRule := truthAbduction

/-- `Truth_ModusPonens` (PLN book §5.7.1, and `lib_pln.metta`). -/
noncomputable def truthModusPonens (p pq : TV) : TV :=
  -- MeTTa hard-codes background probability `c = 0.02`.
  ⟨modusPonens pq.s p.s 0.02, p.c * pq.c⟩

/-- `Truth_SymmetricModusPonens` (OpenCog formula; `lib_pln.metta`). -/
noncomputable def truthSymmetricModusPonens (a ab : TV) : TV :=
  let snotAB : ℝ := 0.2
  let cnotAB : ℝ := 1.0
  let s := a.s * ab.s + snotAB * (1 - a.s) * (1 + ab.s)
  let c := min (min ab.c cnotAB) a.c
  ⟨s, c⟩

/-- `Truth_Revision` (PLN book §5.10.2, and `lib_pln.metta`). -/
noncomputable def truthRevision (t1 t2 : TV) : TV :=
  let w1 := c2w t1.c
  let w2 := c2w t2.c
  let w := w1 + w2
  let f := safeDiv (w1 * t1.s + w2 * t2.s) w
  let c := w2c w
  ⟨min 1 f, min 1 c⟩

/-- `Truth_Negation` (and the PLN "not-elimination" rule) -/
noncomputable def truthNegation (t : TV) : TV :=
  ⟨1 - t.s, t.c⟩

/-! ## Additional `lib_pln.metta` truth functions (WIP/heuristic) -/

/-- `Truth_inversion` (OpenCog WIP; `lib_pln.metta`). -/
noncomputable def truthInversion (b ab : TV) : TV :=
  -- Strength preserved; confidence penalized (MeTTa: `Bc * (ABc * 0.6)`).
  ⟨ab.s, b.c * (ab.c * 0.6)⟩

/-- `Truth_equivalenceToImplication` (OpenCog WIP; `lib_pln.metta`). -/
noncomputable def truthEquivalenceToImplication (a b ab : TV) : TV :=
  let conclS :=
    if 0.99 < ab.s * ab.c then
      ab.s
    else
      safeDiv ((1 + safeDiv b.s a.s) * ab.s) (1 + ab.s)
  ⟨conclS, ab.c⟩

/-- Strength-level helper corresponding to `TransitiveSimilarityStrength` in `lib_pln.metta`. -/
noncomputable def transitiveSimilarityStrength (sim_AB sim_BC s_A s_B s_C : ℝ) : ℝ :=
  transitiveSimilarity sim_AB sim_BC s_A s_B s_C

/-- `Truth_transitiveSimilarity` (OpenCog WIP; `lib_pln.metta`). -/
noncomputable def truthTransitiveSimilarity (a b c ab bc : TV) : TV :=
  let s := transitiveSimilarityStrength ab.s bc.s a.s b.s c.s
  let conf := min ab.c bc.c
  ⟨s, conf⟩

/-- Partial version of `simpleDeductionStrength` (returns `none` when preconditions fail). -/
noncomputable def simpleDeductionStrength (sA sB sC sAB sBC : ℝ) : Option ℝ := by
  classical
  exact
    if conditionalProbabilityConsistency sA sB sAB ∧
       conditionalProbabilityConsistency sB sC sBC then
      if 0.99 < sB then some sC else
        some (sAB * sBC + safeDiv ((1 - sAB) * (sC - sB * sBC)) (1 - sB))
    else
      none

/-- `Truth_evaluationImplication` (OpenCog WIP; `lib_pln.metta`). -/
noncomputable def truthEvaluationImplication (a b c ab ac : TV) : Option TV :=
  match simpleDeductionStrength b.s a.s c.s ab.s ac.s with
  | none => none
  | some s =>
      let conf :=
        (0.9 * 0.9) *
          min b.c (min a.c (min c.c (min ac.c (0.9 * ab.c))))
      some ⟨s, conf⟩

/-! ### Conversions already formalized elsewhere

`lib_pln.metta` contains additional WIP/heuristic truth functions (inversion, equivalence-to-
implication, transitive similarity, evaluation-implication). We map those to the Lean development
via `PLNInferenceRules.lean` (where the strength-level parts are already defined).
-/

/-! ## Small correctness shims (strength-level) -/

theorem truthInduction_s_eq (a b c ba bc : TV) :
    (truthInduction a b c ba bc).s = plnInductionStrength ba.s bc.s a.s b.s c.s := by
  simp [truthInduction]

theorem truthAbduction_s_eq (a b c ab cb : TV) :
    (truthAbduction a b c ab cb).s = plnAbductionStrength ab.s cb.s a.s b.s c.s := by
  simp [truthAbduction]

end Mettapedia.Logic.PLNMettaTruthFunctions
