import Mathlib.Computability.TMConfig
import Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting
import Mettapedia.UniversalAI.TimeBoundedAIXI.ToPartrecEncodable
import Mettapedia.UniversalAI.TimeBoundedAIXI.CodingBits
import Mettapedia.UniversalAI.TimeBoundedAIXI.Core

/-!
# Chapter 7 (core-generic): Step-3 time-bounded execution via `ToPartrec`

`TimeBoundedAIXI.Core` intentionally keeps Chapter 7’s logical schema abstract.
This module instantiates the missing **Step 3** ingredient by providing:

- a generic `History ↔ List ℕ` encoding (for arbitrary finite action/percept alphabets),
- a `ToPartrec.Code` based raw program wrapper,
- time-bounded execution (`evalWithin`) with a total default output,
- an “eventual stabilization as `t → ∞`” lemma for fixed programs/histories.
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI.Core

open scoped Classical

namespace Coding

universe u

/-! ## Fintype elements as naturals -/

noncomputable def encodeFintypeNat {α : Type u} [Fintype α] : α → ℕ :=
  fun a => (Fintype.equivFin α a).val

noncomputable def decodeFintypeNat {α : Type u} [Fintype α] : ℕ → Option α :=
  fun n =>
    if h : n < Fintype.card α then
      some ((Fintype.equivFin α).symm ⟨n, h⟩)
    else
      none

@[simp] theorem decodeFintypeNat_encodeFintypeNat {α : Type u} [Fintype α] (a : α) :
    decodeFintypeNat (encodeFintypeNat a) = some a := by
  classical
  unfold decodeFintypeNat encodeFintypeNat
  set x : Fin (Fintype.card α) := Fintype.equivFin α a
  have hx : x.val < Fintype.card α := x.isLt
  simp [x, hx]

/-! ## Histories as naturals -/

noncomputable def encodeHistElemNat {Action : Type uA} {Percept : Type uP} [Fintype Action] [Fintype Percept] :
    BayesianAgents.Core.HistElem Action Percept → ℕ × ℕ
  -- Shift by `+1` so that `0` can serve as an explicit end-of-history marker
  -- (useful for `ToPartrec` codes that case-split on `0`).
  | .act a => (1, encodeFintypeNat a + 1)
  | .per x => (2, encodeFintypeNat x + 1)

noncomputable def decodeHistElemNat {Action : Type uA} {Percept : Type uP} [Fintype Action] [Fintype Percept]
    (tag payload : ℕ) : Option (BayesianAgents.Core.HistElem Action Percept) :=
  match tag with
  | 1 =>
      if payload = 0 then none else
        (decodeFintypeNat (α := Action) (payload - 1)).map BayesianAgents.Core.HistElem.act
  | 2 =>
      if payload = 0 then none else
        (decodeFintypeNat (α := Percept) (payload - 1)).map BayesianAgents.Core.HistElem.per
  | _ => none

@[simp] theorem decodeHistElemNat_encodeHistElemNat {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] (e : BayesianAgents.Core.HistElem Action Percept) :
    decodeHistElemNat (encodeHistElemNat e).1 (encodeHistElemNat e).2 = some e := by
  cases e <;> simp [encodeHistElemNat, decodeHistElemNat]

noncomputable def encodeHistoryNat {Action : Type uA} {Percept : Type uP} [Fintype Action] [Fintype Percept] :
    BayesianAgents.Core.History Action Percept → List ℕ
  | [] => [0]
  | e :: es =>
      let ep := encodeHistElemNat e
      ep.1 :: ep.2 :: encodeHistoryNat es

noncomputable def decodeHistoryNat {Action : Type uA} {Percept : Type uP} [Fintype Action] [Fintype Percept] :
    List ℕ → Option (BayesianAgents.Core.History Action Percept)
  | [] => some []
  | 0 :: _ => some []
  | tag :: payload :: rest => do
      let e? := decodeHistElemNat (Action := Action) (Percept := Percept) tag payload
      let es? := decodeHistoryNat (Action := Action) (Percept := Percept) rest
      match e?, es? with
      | some e, some es => some (e :: es)
      | _, _ => none
  | _ => none

@[simp] theorem decodeHistoryNat_encodeHistoryNat {Action : Type uA} {Percept : Type uP}
    [Fintype Action] [Fintype Percept] (h : BayesianAgents.Core.History Action Percept) :
    decodeHistoryNat (Action := Action) (Percept := Percept) (encodeHistoryNat (Action := Action) (Percept := Percept) h) =
      some h := by
  induction h with
  | nil =>
      simp [encodeHistoryNat, decodeHistoryNat]
  | cons e es ih =>
      cases e <;> simp [encodeHistoryNat, decodeHistoryNat, encodeHistElemNat, decodeHistElemNat, ih]

/-! ## Program outputs: values/actions -/

noncomputable def decodeValueNat (num den : ℕ) : ℝ :=
  (num : ℝ) / (den + 1 : ℝ)

noncomputable def decodeValueActionOutput {Action : Type uA} [Fintype Action] : List ℕ → Option (ℝ × Action)
  | num :: den :: a :: _ =>
      (decodeFintypeNat (α := Action) a).map fun act => (decodeValueNat num den, act)
  | _ => none

end Coding

/-! ## Raw programs implemented as `ToPartrec.Code` -/

/-- A “raw” extended chronological program implemented as `ToPartrec.Code`.

The raw code computes a `List ℕ` output; `decodeOutput` interprets this as a `(value, action)` pair.
If either evaluation fails to halt within the time budget or decoding fails, we fall back to
`(0, default)`.
-/
structure RawToPartrecProgram (Action : Type uA) (Percept : Type uP) where
  code : Program
  tm : Turing.ToPartrec.Code
  encodeHistory : BayesianAgents.Core.History Action Percept → List ℕ
  decodeOutput : List ℕ → Option (ℝ × Action)

namespace RawToPartrecProgram

variable {Action : Type uA} {Percept : Type uP}

/-- Canonical raw program wrapper using the `Coding` encodings. -/
noncomputable def ofToPartrec [Fintype Action] [Fintype Percept] (bits : List Bool) (tm : Turing.ToPartrec.Code) :
    RawToPartrecProgram Action Percept :=
  { code := { code := bits }
    tm := tm
    encodeHistory := Coding.encodeHistoryNat (Action := Action) (Percept := Percept)
    decodeOutput := Coding.decodeValueActionOutput (Action := Action) }

def decodeToPartrec : ProofDecoder Turing.ToPartrec.Code :=
  fun bits => Mettapedia.UniversalAI.TimeBoundedAIXI.Coding.decodeEncodableBits (α := Turing.ToPartrec.Code) bits

noncomputable def decodeCanonical [Fintype Action] [Fintype Percept] : ProofDecoder (RawToPartrecProgram Action Percept) :=
  fun bits => (decodeToPartrec bits).map (ofToPartrec (Action := Action) (Percept := Percept) bits)

theorem code_length_of_decodeCanonical [Fintype Action] [Fintype Percept] {bits : List Bool}
    {p : RawToPartrecProgram Action Percept} (hdec : decodeCanonical (Action := Action) (Percept := Percept) bits = some p) :
    p.code.length = bits.length := by
  classical
  unfold decodeCanonical at hdec
  cases htm : decodeToPartrec bits with
  | none =>
      simp [htm] at hdec
  | some tm =>
      have hp : ofToPartrec (Action := Action) (Percept := Percept) bits tm = p := by
        simpa [htm] using hdec
      simp [hp.symm, ofToPartrec]

/-- Run a raw program for `t` small steps, producing a total `(value, action)` output by defaulting
to `(0, default)` when evaluation/decoding fails within the budget. -/
def computeWithin {Action : Type uA} {Percept : Type uP} [Inhabited Action] (t : ℕ)
    (p : RawToPartrecProgram Action Percept) (h : BayesianAgents.Core.History Action Percept) : ℝ × Action :=
  match Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.evalWithin t p.tm (p.encodeHistory h) with
  | some out => (p.decodeOutput out).getD (0, default)
  | none => (0, default)

/-- The associated total extended chronological program (post-modification). -/
def toExtended {Action : Type uA} {Percept : Type uP} [Inhabited Action] (t : ℕ) (p : RawToPartrecProgram Action Percept) :
    ExtendedChronologicalProgram Action Percept :=
  { code := p.code
    compute := computeWithin (Action := Action) (Percept := Percept) t p }

/-- Unbounded semantics for a raw `ToPartrec` program, defaulting to `(0, default)` when evaluation does
not terminate (or decoding fails). -/
noncomputable def computeUnbounded {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (p : RawToPartrecProgram Action Percept) (h : BayesianAgents.Core.History Action Percept) : ℝ × Action := by
  classical
  exact
    if hDom : (p.tm.eval (p.encodeHistory h)).Dom then
      (p.decodeOutput ((p.tm.eval (p.encodeHistory h)).get hDom)).getD (0, default)
    else
      (0, default)

@[simp] theorem computeUnbounded_of_dom {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (p : RawToPartrecProgram Action Percept) (h : BayesianAgents.Core.History Action Percept)
    (hDom : (p.tm.eval (p.encodeHistory h)).Dom) :
    p.computeUnbounded h =
      (p.decodeOutput ((p.tm.eval (p.encodeHistory h)).get hDom)).getD (0, default) := by
  classical
  simp [RawToPartrecProgram.computeUnbounded, hDom]

@[simp] theorem computeUnbounded_of_not_dom {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (p : RawToPartrecProgram Action Percept) (h : BayesianAgents.Core.History Action Percept)
    (hDom : ¬ (p.tm.eval (p.encodeHistory h)).Dom) :
    p.computeUnbounded h = (0, default) := by
  classical
  simp [RawToPartrecProgram.computeUnbounded, hDom]

/-- The associated extended chronological program using unbounded `ToPartrec` semantics. -/
noncomputable def toExtendedUnbounded {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (p : RawToPartrecProgram Action Percept) : ExtendedChronologicalProgram Action Percept :=
  { code := p.code
    compute := p.computeUnbounded }

/-- If we increase the fuel, a time-bounded run stabilizes to the unbounded semantics. -/
theorem exists_computeWithin_eq_computeUnbounded {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (p : RawToPartrecProgram Action Percept) (h : BayesianAgents.Core.History Action Percept) :
    ∃ N, ∀ t ≥ N, computeWithin (Action := Action) (Percept := Percept) t p h = p.computeUnbounded h := by
  classical
  by_cases hDom : (p.tm.eval (p.encodeHistory h)).Dom
  · let out : List ℕ := (p.tm.eval (p.encodeHistory h)).get hDom
    have hout : out ∈ p.tm.eval (p.encodeHistory h) := by
      simpa [out] using (Part.get_mem (o := p.tm.eval (p.encodeHistory h)) hDom)
    have hex :
        ∃ n, Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.evalWithin n p.tm (p.encodeHistory h) =
          some out :=
      (Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.exists_evalWithin_eq_some_iff
        (c := p.tm) (v := p.encodeHistory h) (out := out)).2 hout
    rcases hex with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro t ht
    have ht' :
        Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.evalWithin t p.tm (p.encodeHistory h) =
          some out :=
      Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.evalWithin_mono (h := hn) (hnm := ht)
    simp [RawToPartrecProgram.computeWithin, RawToPartrecProgram.computeUnbounded, hDom, out, ht']
  · refine ⟨0, ?_⟩
    intro t _ht
    have ht' :
        Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.evalWithin t p.tm (p.encodeHistory h) = none := by
      cases hrun :
          Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.evalWithin t p.tm (p.encodeHistory h) with
      | none => rfl
      | some out =>
          exfalso
          have hout : out ∈ p.tm.eval (p.encodeHistory h) :=
            Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.ToPartrec.evalWithin_sound
              (c := p.tm) (v := p.encodeHistory h) (out := out) hrun
          rcases hout with ⟨hDom', _houtEq⟩
          exact hDom hDom'
    simp [RawToPartrecProgram.computeWithin, RawToPartrecProgram.computeUnbounded, hDom, ht']

/-- Transport a pointwise equality on a raw list to equality of `bestByValueAux` on the corresponding
extended-program lists. -/
theorem bestByValueAux_map_toExtended_eq_of_forall {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (acc : ℝ × Action) (programs : List (RawToPartrecProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) (t : ℕ)
    (hall : ∀ p ∈ programs, computeWithin (Action := Action) (Percept := Percept) t p h = p.computeUnbounded h) :
    bestByValueAux acc (programs.map (fun p => p.toExtended (Action := Action) (Percept := Percept) t)) h =
      bestByValueAux acc (programs.map (fun p => p.toExtendedUnbounded (Action := Action) (Percept := Percept))) h := by
  induction programs generalizing acc with
  | nil =>
      simp [bestByValueAux]
  | cons p ps ih =>
      have hp : computeWithin (Action := Action) (Percept := Percept) t p h = p.computeUnbounded h := hall p (by simp)
      have hallTail :
          ∀ q ∈ ps, computeWithin (Action := Action) (Percept := Percept) t q h = q.computeUnbounded h := by
        intro q hq
        exact hall q (by simp [hq])
      have ih' := ih (acc := selectBetter acc (p.computeUnbounded h)) (hall := hallTail)
      simpa [bestByValueAux, List.foldl_cons, RawToPartrecProgram.toExtended, RawToPartrecProgram.toExtendedUnbounded, hp]
        using ih'

/-- Transport a pointwise equality on a raw list to equality of `bestByValue`. -/
theorem bestByValue_map_toExtended_eq_of_forall {Action : Type uA} {Percept : Type uP} [Inhabited Action]
    (programs : List (RawToPartrecProgram Action Percept)) (h : BayesianAgents.Core.History Action Percept) (t : ℕ)
    (hall : ∀ p ∈ programs, computeWithin (Action := Action) (Percept := Percept) t p h = p.computeUnbounded h) :
    bestByValue (programs.map (fun p => p.toExtended (Action := Action) (Percept := Percept) t)) h =
      bestByValue (programs.map (fun p => p.toExtendedUnbounded (Action := Action) (Percept := Percept))) h := by
  cases programs with
  | nil =>
      simp [bestByValue]
  | cons p0 ps =>
      have hp0 : computeWithin (Action := Action) (Percept := Percept) t p0 h = p0.computeUnbounded h := hall p0 (by simp)
      have hallTail :
          ∀ q ∈ ps, computeWithin (Action := Action) (Percept := Percept) t q h = q.computeUnbounded h := by
        intro q hq
        exact hall q (by simp [hq])
      have haux :=
        bestByValueAux_map_toExtended_eq_of_forall (Action := Action) (Percept := Percept)
          (acc := p0.computeUnbounded h) (programs := ps) (h := h) (t := t) (hall := hallTail)
      simpa [bestByValue, RawToPartrecProgram.toExtended, RawToPartrecProgram.toExtendedUnbounded, hp0] using haux

/-- For a fixed raw program list and history, there is a single fuel bound beyond which all wrapped
computations agree with the unbounded semantics. -/
theorem exists_fuel_bound_forall_computeWithin_eq_computeUnbounded {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] (programs : List (RawToPartrecProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) :
    ∃ N, ∀ p ∈ programs, ∀ t ≥ N, computeWithin (Action := Action) (Percept := Percept) t p h = p.computeUnbounded h := by
  classical
  induction programs with
  | nil =>
      refine ⟨0, ?_⟩
      intro p hp
      cases hp
  | cons p ps ih =>
      rcases exists_computeWithin_eq_computeUnbounded (Action := Action) (Percept := Percept) (p := p) (h := h) with
        ⟨Np, hNp⟩
      rcases ih with ⟨Nps, hNps⟩
      refine ⟨Nat.max Np Nps, ?_⟩
      intro q hq t ht
      simp [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hNp t (le_trans (Nat.le_max_left _ _) ht)
      · exact hNps q hq t (le_trans (Nat.le_max_right _ _) ht)

/-- For a fixed raw program list and history, `bestByValue` on the time-bounded wrappers stabilizes
to the unbounded semantics. -/
theorem exists_fuel_bound_bestByValue_eq_unbounded {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] (programs : List (RawToPartrecProgram Action Percept))
    (h : BayesianAgents.Core.History Action Percept) :
    ∃ N, ∀ t ≥ N,
      bestByValue (programs.map (fun p => p.toExtended (Action := Action) (Percept := Percept) t)) h =
        bestByValue (programs.map (fun p => p.toExtendedUnbounded (Action := Action) (Percept := Percept))) h := by
  classical
  rcases
      exists_fuel_bound_forall_computeWithin_eq_computeUnbounded (Action := Action) (Percept := Percept)
        (programs := programs) (h := h) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro t ht
  refine bestByValue_map_toExtended_eq_of_forall (Action := Action) (Percept := Percept) (programs := programs) (h := h)
    (t := t) ?_
  intro p hp
  exact hN p hp t ht

end RawToPartrecProgram

/-! ## Building AIXItl using the concrete Step-3 wrapper -/

namespace AIXItl

open RawToPartrecProgram

variable {Action : Type uA} {Percept : Type uP} [Inhabited Action] [Fintype Action] [Fintype Percept]
  [BayesianAgents.Core.PerceptReward Percept]

/-- Step‑2/3: filter raw programs by code length and wrap them with the time budget. -/
def filterAndModifyToPartrec (programs : List (RawToPartrecProgram Action Percept)) (l t : ℕ) :
    List (ExtendedChronologicalProgram Action Percept) :=
  (programs.filter fun p => p.code.length ≤ l).map fun p => p.toExtended (Action := Action) (Percept := Percept) t

omit [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept] in
theorem length_filterAndModifyToPartrec_le (programs : List (RawToPartrecProgram Action Percept)) (l t : ℕ) :
    (filterAndModifyToPartrec (Action := Action) (Percept := Percept) programs l t).length ≤ programs.length := by
  classical
  simp [filterAndModifyToPartrec, List.length_filter_le]

omit [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept] in
theorem perCycleSteps_filterAndModifyToPartrec_le (programs : List (RawToPartrecProgram Action Percept)) (l t : ℕ) :
    (filterAndModifyToPartrec (Action := Action) (Percept := Percept) programs l t).length * t ≤ programs.length * t := by
  exact Nat.mul_le_mul_right t (length_filterAndModifyToPartrec_le (Action := Action) (Percept := Percept) programs l t)

/-- AIXItl instantiated from a proof checker over raw `ToPartrec` programs. -/
noncomputable def aixitlFromProofCheckerToPartrec
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (horizon : ℕ)
    (t : ℕ)
    (checker :
      ProofChecker (α := RawToPartrecProgram Action Percept)
        (fun p => ValidValueLowerBound μ γ horizon (p.toExtended (Action := Action) (Percept := Percept) t)))
    (l l_p : ℕ) : AIXItl Action Percept :=
  { timeBound := t
    lengthBound := l
    proofLengthBound := l_p
    validatedPrograms := filterAndModifyToPartrec (Action := Action) (Percept := Percept) (findValidPrograms checker.decode l_p) l t }

theorem perCycleSteps_aixitlFromProofCheckerToPartrec_le
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (horizon : ℕ)
    (t : ℕ)
    (checker :
      ProofChecker (α := RawToPartrecProgram Action Percept)
        (fun p => ValidValueLowerBound μ γ horizon (p.toExtended (Action := Action) (Percept := Percept) t)))
    (l l_p : ℕ) :
    (aixitlFromProofCheckerToPartrec (Action := Action) (Percept := Percept) μ γ horizon t checker l l_p).validatedPrograms.length *
        t ≤
      (findValidPrograms checker.decode l_p).length * t := by
  simpa [aixitlFromProofCheckerToPartrec] using
    perCycleSteps_filterAndModifyToPartrec_le (Action := Action) (Percept := Percept)
      (programs := findValidPrograms checker.decode l_p) (l := l) (t := t)

theorem validValueLowerBound_of_mem_aixitlFromProofCheckerToPartrec
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (horizon : ℕ)
    (t : ℕ)
    (checker :
      ProofChecker (α := RawToPartrecProgram Action Percept)
        (fun p => ValidValueLowerBound μ γ horizon (p.toExtended (Action := Action) (Percept := Percept) t)))
    (l l_p : ℕ) {p : ExtendedChronologicalProgram Action Percept}
    (hp : p ∈ (aixitlFromProofCheckerToPartrec (Action := Action) (Percept := Percept) μ γ horizon t checker l l_p).validatedPrograms) :
    ValidValueLowerBound μ γ horizon p := by
  -- Membership gives some raw `q` with `q.toExtended t = p` and a decoded proof.
  classical
  simp [aixitlFromProofCheckerToPartrec, filterAndModifyToPartrec] at hp
  rcases hp with ⟨q, hq, hpEq⟩
  subst hpEq
  exact ProofChecker.sound_of_mem_findValidPrograms (checker := checker) (ha := hq.1)

/-! ## ε-optimality / convergence schema for the `ToPartrec` instantiation -/

theorem aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_eventually_of_exists_good_program
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (l t : ℕ) (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (checker :
      CompleteProofChecker (α := RawToPartrecProgram Action Percept)
        (fun p => ValidValueLowerBound μ γ (n + 1) (p.toExtended (Action := Action) (Percept := Percept) t)))
    (hex :
      ∃ p : RawToPartrecProgram Action Percept,
        p.code.length ≤ l ∧
          ValidValueLowerBound μ γ (n + 1) (p.toExtended (Action := Action) (Percept := Percept) t) ∧
            BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
              ((p.toExtended (Action := Action) (Percept := Percept) t).compute h).1) :
    ∃ N, ∀ l_p ≥ N,
      BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
        BayesianAgents.Core.optimalQValue μ γ h
          (aixitl_cycle
            (aixitlFromProofCheckerToPartrec (Action := Action) (Percept := Percept) μ γ (n + 1) t
              checker.toProofChecker l l_p) h)
          n := by
  classical
  rcases hex with ⟨p, hpLen, hpValid, hpClaim⟩
  rcases
      CompleteProofChecker.exists_bound_forall_mem_findValidPrograms (checker := checker) (a := p) hpValid with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro l_p hlp
  let agent :=
    aixitlFromProofCheckerToPartrec (Action := Action) (Percept := Percept) μ γ (n + 1) t checker.toProofChecker l l_p
  have hpMem : p ∈ findValidPrograms checker.decode l_p := hN l_p hlp
  have hpExtMem :
      (p.toExtended (Action := Action) (Percept := Percept) t) ∈ agent.validatedPrograms := by
    simp [agent, aixitlFromProofCheckerToPartrec, filterAndModifyToPartrec]
    exact ⟨p, ⟨hpMem, hpLen⟩, rfl⟩
  have hne : agent.validatedPrograms ≠ [] := List.ne_nil_of_mem hpExtMem
  have hall : ∀ q ∈ agent.validatedPrograms, ValidValueLowerBound μ γ (n + 1) q := by
    intro q hq
    refine
      validValueLowerBound_of_mem_aixitlFromProofCheckerToPartrec (Action := Action) (Percept := Percept) (μ := μ)
        (γ := γ) (horizon := n + 1) (t := t) (checker := checker.toProofChecker) (l := l) (l_p := l_p)
        (hp := ?_)
    simpa [agent] using hq
  have hex' :
      ∃ q ∈ agent.validatedPrograms,
        BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
          (q.compute h).1 := by
    refine ⟨p.toExtended (Action := Action) (Percept := Percept) t, hpExtMem, ?_⟩
    simpa using hpClaim
  simpa [agent] using
    (aixitl_cycle_eps_optimal (Action := Action) (Percept := Percept) (agent := agent) (μ := μ) (γ := γ) (h := h)
      (n := n) (ε := ε) (hwf := hwf) (hne := hne) (hall := hall) (hex := hex'))

/-- There exists a time bound `t` and a verified raw program whose claimed value is within `ε`
of optimal at history `h`. -/
def ExistsNearOptimalVerifiedRawProgram
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ t : ℕ,
    ∃ p : RawToPartrecProgram Action Percept,
      ValidValueLowerBound μ γ (n + 1) (p.toExtended (Action := Action) (Percept := Percept) t) ∧
        BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
          ((p.toExtended (Action := Action) (Percept := Percept) t).compute h).1

def HasNearOptimalVerifiedRawPrograms
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ExistsNearOptimalVerifiedRawProgram (Action := Action) (Percept := Percept) μ γ h n ε

def HasNearOptimalVerifiedRawProgramsForAllHistories
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (n : ℕ) : Prop :=
  ∀ h : BayesianAgents.Core.History Action Percept,
    BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
      HasNearOptimalVerifiedRawPrograms (Action := Action) (Percept := Percept) μ γ h n

theorem aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ) (ε : ℝ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (checkerFamily :
      CompleteProofCheckerFamily (α := RawToPartrecProgram Action Percept)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended (Action := Action) (Percept := Percept) t)))
    (hex : ExistsNearOptimalVerifiedRawProgram (Action := Action) (Percept := Percept) μ γ h n ε) :
    ∃ t l N, ∀ l_p ≥ N,
      BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
        BayesianAgents.Core.optimalQValue μ γ h
          (aixitl_cycle
            (aixitlFromProofCheckerToPartrec (Action := Action) (Percept := Percept) μ γ (n + 1) t
              (checkerFamily.checker t).toProofChecker l l_p) h)
          n := by
  classical
  rcases hex with ⟨t, p, hpValid, hpClaim⟩
  rcases
      aixitlFromCompleteProofCheckerToPartrec_cycle_eps_optimal_eventually_of_exists_good_program
        (Action := Action) (Percept := Percept) (μ := μ) (γ := γ) (l := p.code.length) (t := t) (h := h) (n := n)
        (ε := ε) (hwf := hwf) (checker := checkerFamily.checker t)
        (hex := ⟨p, Nat.le_refl _, hpValid, hpClaim⟩) with
    ⟨N, hN⟩
  refine ⟨t, p.code.length, N, ?_⟩
  intro l_p hlp
  exact hN l_p hlp

theorem aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually_of_forall
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor)
    (h : BayesianAgents.Core.History Action Percept) (n : ℕ)
    (hwf : BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h)
    (checkerFamily :
      CompleteProofCheckerFamily (α := RawToPartrecProgram Action Percept)
        (fun t p => ValidValueLowerBound μ γ (n + 1) (p.toExtended (Action := Action) (Percept := Percept) t)))
    (hex : HasNearOptimalVerifiedRawPrograms (Action := Action) (Percept := Percept) μ γ h n) :
    ∀ ε : ℝ, 0 < ε →
      ∃ t l N, ∀ l_p ≥ N,
        BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤
          BayesianAgents.Core.optimalQValue μ γ h
            (aixitl_cycle
              (aixitlFromProofCheckerToPartrec (Action := Action) (Percept := Percept) μ γ (n + 1) t
                (checkerFamily.checker t).toProofChecker l l_p) h)
            n := by
  intro ε hε
  exact
    aixitlFromCompleteProofCheckerFamilyToPartrec_cycle_eps_optimal_eventually (Action := Action) (Percept := Percept)
      (μ := μ) (γ := γ) (h := h) (n := n) (ε := ε) (hwf := hwf) (checkerFamily := checkerFamily)
      (hex := hex ε hε)

end AIXItl

end Mettapedia.UniversalAI.TimeBoundedAIXI.Core
