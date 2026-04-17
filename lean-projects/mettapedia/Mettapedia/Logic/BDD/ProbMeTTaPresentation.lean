import Mettapedia.Logic.BDD.ProbMeTTaStateSpace
import Mathlib.Data.Real.Basic

/-!
# ProbMeTTa Presentation Layer

This file formalizes the user-visible presentation layer from
`/home/zar/claude/ProbMeTTa/lib_prob.metta`:

- `round-to`
- top-level `?prob`
- top-level `?prob-given`

The important point here is exact source-shape alignment: the exposed top-level
outputs are no longer described informally as “just the exact probability.” They
are the exact probability passed through the explicit rounding operator.

Positive example:
- `probPresented` is literally `roundTo5` of the exact `probExact` value.

Negative example:
- this file does not try to prove floating-point error bounds or emulate every
  numeric backend detail of MeTTa. It captures the intended `round-math`
  presentation formula.
-/

namespace Mettapedia.Logic.BDDCore

open scoped ENNReal
open Mettapedia.Logic.LP

/-- Scaling factor used by the source `(round-to x digits)` operator. -/
noncomputable def roundToFactor (digits : ℕ) : ℝ := (10 : ℝ) ^ digits

/-- Exact source-style decimal rounding: `round(x * 10^digits) / 10^digits`.
We encode `round` by the standard `floor (y + 1/2)` presentation. -/
noncomputable def roundToReal (digits : ℕ) (x : ℝ) : ℝ :=
  ((Int.floor (x * roundToFactor digits + (1 / 2 : ℝ)) : Int) : ℝ) /
    roundToFactor digits

/-- The literal top-level ProbMeTTa presentation uses five digits. -/
noncomputable def roundTo5 (x : ℝ) : ℝ :=
  roundToReal 5 x

@[simp] theorem roundTo5_eq_roundToReal (x : ℝ) :
    roundTo5 x = roundToReal 5 x := rfl

/-- Literal top-level `?prob` output for the normalized source program. -/
noncomputable def ProbMeTTaSourceProgram.probPresented
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) : ℝ :=
  roundTo5 (prog.probExact s q).toReal

/-- Literal top-level `?prob-given` output for the normalized source program. -/
noncomputable def ProbMeTTaSourceProgram.probGivenPresented
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) : ℝ :=
  roundTo5 (prog.probGivenViaOperatorsExact s q evidence).toReal

@[simp] theorem ProbMeTTaSourceProgram.probPresented_eq_roundTo5
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) :
    prog.probPresented s q = roundTo5 (prog.probExact s q).toReal := rfl

@[simp] theorem ProbMeTTaSourceProgram.probGivenPresented_eq_roundTo5
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    prog.probGivenPresented s q evidence =
      roundTo5 (prog.probGivenViaOperatorsExact s q evidence).toReal := rfl

/-- Literal top-level `?prob` output for the explicit state-space model. -/
noncomputable def ProbMeTTaSpaceState.presentProb
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (q : GroundAtom σ) : ℝ :=
  state.toSourceProgram.probPresented s q

/-- Literal top-level `?prob-given` output for the explicit state-space model. -/
noncomputable def ProbMeTTaSpaceState.presentProbGiven
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) : ℝ :=
  state.toSourceProgram.probGivenPresented s q evidence

@[simp] theorem ProbMeTTaSpaceState.presentProb_eq_roundTo5
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ) (q : GroundAtom σ) :
    state.presentProb s q = roundTo5 (state.toSourceProgram.probExact s q).toReal := rfl

@[simp] theorem ProbMeTTaSpaceState.presentProbGiven_eq_roundTo5
    {σ : LPSignature}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (state : ProbMeTTaSpaceState σ)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    state.presentProbGiven s q evidence =
      roundTo5 (state.toSourceProgram.probGivenViaOperatorsExact s q evidence).toReal := rfl

/-- The explicit source-level `round-to 5` theorem for `?prob`. -/
theorem probmetta_prob_output_eq_roundTo5
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ) (q : GroundAtom σ) :
    prog.probPresented s q = roundToReal 5 (prog.probExact s q).toReal := by
  rfl

/-- The explicit source-level `round-to 5` theorem for `?prob-given`. -/
theorem probmetta_probGiven_output_eq_roundTo5
    {σ : LPSignature} {n : ℕ}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbMeTTaSourceProgram σ n)
    (s : Stratification σ)
    (q : GroundAtom σ) (evidence : List (GroundAtom σ)) :
    prog.probGivenPresented s q evidence =
      roundToReal 5 (prog.probGivenViaOperatorsExact s q evidence).toReal := by
  rfl

end Mettapedia.Logic.BDDCore
