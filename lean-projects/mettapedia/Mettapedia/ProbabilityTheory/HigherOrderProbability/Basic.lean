import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mettapedia.ProbabilityTheory.Basic

/-!
# Higher-Order Probabilities: Basic Definitions

This file introduces the foundational structures for higher-order probability theory,
establishing the framework for Kyburg's flattening theorem.

## Main Definitions

* `ParametrizedDistribution` : A Markov kernel κ : Θ → Measure X together with a mixing
  measure μ over parameters. This represents "uncertainty about which distribution governs X".

* `kyburgJoint` : The joint distribution P(θ, x) = μ ⊗ₘ κ

* `flatten` : The flattened/marginal distribution κ ∘ₘ μ = ∫ κ(θ) dμ(θ)

## Key Design Choice

We use mathlib's `ProbabilityTheory.Kernel` structure with `IsMarkovKernel` constraint.
This gives us:
- Correct measurability (Kernel has `Measurable κ` built in)
- `κ.aemeasurable` for free
- `IsProbabilityMeasure (κ ∘ₘ μ)` instance from mathlib when μ is probability and κ is Markov

## References

- Kyburg, H.E. (1988). "Higher Order Probabilities"
- Giry, M. (1982). "A categorical approach to probability theory"
- Mathlib: ProbabilityTheory.Kernel, MeasureTheory.Measure.bind

-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-! ## Parametrized Distribution

Using mathlib's Kernel structure for correct measurability.
-/

/-- A parametrized family of distributions with mixing measure.

This structure represents:
- `kernel` : A Markov kernel Θ → Measure X (the possible "true" distributions)
- `mixingMeasure` : Probability measure over parameters (the "uncertainty")

Together these encode a "second-order" probability: we don't know which distribution
governs X, so we have a distribution (mixingMeasure) over possible distributions (kernel).
-/
structure Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution
    (Θ X : Type*) [MeasurableSpace Θ] [MeasurableSpace X] where
  /-- Markov kernel: family of probability distributions indexed by Θ -/
  kernel : Kernel Θ X
  /-- The kernel is a Markov kernel (each kernel(θ) is a probability measure) -/
  kernel_isMarkov : ProbabilityTheory.IsMarkovKernel kernel
  /-- Probability measure over parameters -/
  mixingMeasure : Measure Θ
  /-- The mixing measure is a probability measure -/
  mixing_isProbability : IsProbabilityMeasure mixingMeasure

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

/-! ### Instance Declarations -/

instance instIsMarkovKernel (pd : ParametrizedDistribution Θ X) :
    ProbabilityTheory.IsMarkovKernel pd.kernel :=
  pd.kernel_isMarkov

instance instIsProbKernel (pd : ParametrizedDistribution Θ X) (θ : Θ) :
    IsProbabilityMeasure (pd.kernel θ) :=
  inferInstance  -- Uses IsMarkovKernel.is_probability_measure'

instance instIsProbMixing (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure pd.mixingMeasure :=
  pd.mixing_isProbability

/-! ### Flattening (Marginalization) -/

/-- Flatten to get marginal distribution on X: P(x) = ∫ kernel(θ)(x) dμ(θ).

This is `κ ∘ₘ μ` in mathlib notation, which equals `μ.bind κ`.

**Kyburg's Insight**: This flattened distribution gives the same predictions as
maintaining the full higher-order structure.
-/
noncomputable def flatten (pd : ParametrizedDistribution Θ X) : Measure X :=
  pd.mixingMeasure.bind pd.kernel

/-- The flattened distribution is a probability measure. -/
instance flatten_isProbability (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure (flatten pd) := by
  unfold flatten
  infer_instance

/-! ### The Joint Distribution -/

/-- The joint distribution P(θ, x) = μ ⊗ₘ κ.

This is Kyburg's construction: from a "second-order" probability, construct
a joint distribution over (parameter, observation) pairs.
-/
noncomputable def kyburgJoint (pd : ParametrizedDistribution Θ X) : Measure (Θ × X) :=
  pd.mixingMeasure.compProd pd.kernel

/-- The joint distribution is a probability measure -/
instance kyburgJoint_isProbability (pd : ParametrizedDistribution Θ X) :
    IsProbabilityMeasure (kyburgJoint pd) := by
  unfold kyburgJoint
  infer_instance

/-! ### Basic Properties -/

/-- The measure of a set under the flattened distribution -/
theorem flatten_apply (pd : ParametrizedDistribution Θ X) (s : Set X) (hs : MeasurableSet s) :
    (flatten pd) s = ∫⁻ θ, (pd.kernel θ) s ∂pd.mixingMeasure := by
  unfold flatten
  rw [Measure.bind_apply hs pd.kernel.aemeasurable]

/-- Flatten is the marginal of the joint over X -/
theorem flatten_eq_snd_kyburgJoint (pd : ParametrizedDistribution Θ X) :
    flatten pd = (kyburgJoint pd).snd := by
  unfold flatten kyburgJoint
  rw [Measure.snd_compProd]

/-- The mixing measure is the marginal of the joint over Θ -/
theorem mixingMeasure_eq_fst_kyburgJoint (pd : ParametrizedDistribution Θ X) :
    pd.mixingMeasure = (kyburgJoint pd).fst := by
  unfold kyburgJoint
  rw [Measure.fst_compProd]

/-! ## Examples and Special Cases -/

/-! ### Example: Countable Parameter Space

For countable parameter spaces, the construction simplifies to a weighted sum.
-/

/-- In the countable case, flattening is a weighted sum -/
theorem flatten_eq_sum_countable [Countable Θ] [MeasurableSingletonClass Θ]
    (pd : ParametrizedDistribution Θ X) :
    flatten pd = Measure.sum (fun θ => pd.mixingMeasure {θ} • pd.kernel θ) := by
  unfold flatten
  exact Measure.comp_eq_sum_of_countable

/-! ### Example: Deterministic Kernel -/

/-- If the kernel is deterministic, flattening gives the pushforward of the mixing measure. -/
theorem flatten_deterministic {Y : Type*} [MeasurableSpace Y]
    (f : Θ → Y) (hf : Measurable f)
    (μ : Measure Θ) [IsProbabilityMeasure μ] :
    (Kernel.deterministic f hf) ∘ₘ μ = μ.map f :=
  Measure.deterministic_comp_eq_map hf

end Mettapedia.ProbabilityTheory.HigherOrderProbability.ParametrizedDistribution
