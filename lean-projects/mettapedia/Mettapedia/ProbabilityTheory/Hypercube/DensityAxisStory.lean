import Mettapedia.ProbabilityTheory.Hypercube.Basic
import Mettapedia.ProbabilityTheory.Hypercube.ScaleDichotomy

/-!
# Density Axis Story: Discrete (ℤ-like) vs Dense (ℚ-like) Scales

`Hypercube/Basic.lean` treats `DensityAxis` as an *assumption axis* (“do we assume the scale is dense?”).

When a theory is represented on a real-valued (additive) scale, the *actual* value scale is an
additive subgroup of some archimedean ordered group (typically `ℝ`). Mathlib’s theorem
`AddSubgroup.dense_or_cyclic` says such subgroups are either:

* **dense** (ℚ-like), or
* **cyclic** (`ℤ • g`, i.e. discrete/step-like).

This file is a small bridge between:

- the *axis-level* `DensityAxis`, and
- the *representation-level* dense-vs-cyclic dichotomy (`Hypercube/ScaleDichotomy.lean`).
-/

namespace Mettapedia.ProbabilityTheory.Hypercube

namespace DensityAxisStory

open Set
open Classical

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]

/-- Classify a concrete value scale (an additive subgroup) by whether it is dense. -/
noncomputable def densityAxisOfSubgroup (S : AddSubgroup G) : DensityAxis :=
  if Dense (S : Set G) then .dense else .nondense

theorem densityAxisOfSubgroup_eq_dense_iff (S : AddSubgroup G) :
    densityAxisOfSubgroup (G := G) S = .dense ↔ Dense (S : Set G) := by
  by_cases h : Dense (S : Set G) <;> simp [densityAxisOfSubgroup, h]

theorem densityAxisOfSubgroup_eq_nondense_iff (S : AddSubgroup G) :
    densityAxisOfSubgroup (G := G) S = .nondense ↔ ¬ Dense (S : Set G) := by
  by_cases h : Dense (S : Set G) <;> simp [densityAxisOfSubgroup, h]

section Ordered

variable [LinearOrder G] [IsOrderedAddMonoid G] [OrderTopology G] [Archimedean G]

section DenseVsZ

variable [Nontrivial G] [DenselyOrdered G]

/-- In the archimedean setting, “dense” is equivalent to “not a discrete ℤ-scale”. -/
theorem densityAxisOfSubgroup_eq_dense_iff_ne_zmultiples (S : AddSubgroup G) :
    densityAxisOfSubgroup (G := G) S = .dense ↔
      ∀ g : G, S ≠ AddSubgroup.zmultiples g := by
  -- Reduce to `Dense (S : Set G)` using the definition of `densityAxisOfSubgroup`,
  -- then apply the standard subgroup dichotomy lemma.
  exact
    (densityAxisOfSubgroup_eq_dense_iff (G := G) (S := S)).trans
      (ScaleDichotomy.dense_iff_ne_zmultiples (S := S))

end DenseVsZ

/-- In the archimedean setting, non-density forces the value scale to be cyclic (`ℤ • g`). -/
theorem densityAxisOfSubgroup_eq_nondense_implies_zmultiples (S : AddSubgroup G)
    (h : densityAxisOfSubgroup (G := G) S = .nondense) :
    ∃ g : G, S = AddSubgroup.zmultiples g := by
  have hNotDense : ¬ Dense (S : Set G) :=
    (densityAxisOfSubgroup_eq_nondense_iff (G := G) (S := S)).1 h
  rcases ScaleDichotomy.dense_or_zmultiples (S := S) with hDense | hz
  · exact (hNotDense hDense).elim
  · exact hz

end Ordered

end DensityAxisStory

end Mettapedia.ProbabilityTheory.Hypercube
