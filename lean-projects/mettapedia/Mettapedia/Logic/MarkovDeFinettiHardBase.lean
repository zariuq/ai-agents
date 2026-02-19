import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Markov de Finetti Hard Base (Active Minimal Surface)

Minimal definitions needed by active Fortini/anchor modules:
`MarkovParam`, `stepProb`, `initProb`, and `wordProb`.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped NNReal ENNReal
open MeasureTheory

namespace MarkovDeFinettiHard

variable {k : ℕ}

structure MarkovParam (k : ℕ) where
  init : ProbabilityMeasure (Fin k)
  trans : Fin k → ProbabilityMeasure (Fin k)

instance : MeasurableSpace (MarkovParam k) := ⊤

def stepProb (θ : MarkovParam k) (a b : Fin k) : ℝ≥0 :=
  θ.trans a (Set.singleton b)

def initProb (θ : MarkovParam k) (a : Fin k) : ℝ≥0 :=
  θ.init (Set.singleton a)

def wordProbAux (θ : MarkovParam k) (a : Fin k) : List (Fin k) → ℝ≥0
  | [] => 1
  | b :: xs => stepProb (k := k) θ a b * wordProbAux θ b xs

def wordProbNN (θ : MarkovParam k) : List (Fin k) → ℝ≥0
  | [] => 1
  | a :: xs => initProb (k := k) θ a * wordProbAux (k := k) θ a xs

def wordProb (θ : MarkovParam k) (xs : List (Fin k)) : ℝ≥0∞ :=
  (wordProbNN (k := k) θ xs : ℝ≥0∞)

end MarkovDeFinettiHard
end Mettapedia.Logic
