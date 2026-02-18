import Exchangeability.DeFinetti.TheoremViaL2

/-!
# External Exchangeability Bridge

Minimal bridge from the vendored `exchangeability` package into
`Mettapedia.CategoryTheory`.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Minimal bridge theorem:
if a real-valued process is exchangeable and square-integrable in each
coordinate, use the external L² de Finetti theorem to obtain
`ConditionallyIID`. -/
theorem deFinettiExternal_viaL2_exchangeable_implies_conditionallyIID
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i : ℕ, Measurable (X i))
    (hX_exch : Exchangeability.Exchangeable μ X)
    (hX_L2 : ∀ i : ℕ, MemLp (X i) 2 μ) :
    Exchangeability.ConditionallyIID μ X :=
  Exchangeability.DeFinetti.deFinetti_viaL2 μ X hX_meas hX_exch hX_L2

end Mettapedia.CategoryTheory

