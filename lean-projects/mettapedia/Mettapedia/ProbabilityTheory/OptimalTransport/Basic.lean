import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Discrete Optimal Transport (PMF)

This file provides a small, `sorry`-free foundation for **distributional optimal transport**
in the discrete setting, aimed at supporting Goertzel's *TransWeave* framework
(`TransWeave_v3.pdf`, Definition 28).

We work with probability mass functions `PMF α` and define:

* `IsCoupling π μ ν` for `π : PMF (α × β)` with marginals `μ : PMF α` and `ν : PMF β`
* `couplingCost π c := ∑' z, π z * c z`
* `kantorovichCost μ ν c` as the infimum of `couplingCost` over all couplings

This is intentionally lightweight: we do **not** attempt to prove the full Wasserstein
metric properties here; we only set up robust definitions and basic lemmas.
-/

noncomputable section

namespace Mettapedia.ProbabilityTheory.OptimalTransport

open scoped Classical BigOperators

open PMF

variable {α β : Type*}

/-- A coupling of `μ : PMF α` and `ν : PMF β` is a joint distribution with the right marginals. -/
def IsCoupling (π : PMF (α × β)) (μ : PMF α) (ν : PMF β) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = ν

/-- The independent (product) coupling: sample `a ∼ μ` and `b ∼ ν` independently. -/
noncomputable def independentCoupling (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind (fun a => (ν.map (fun b => (a, b))))

theorem isCoupling_independentCoupling (μ : PMF α) (ν : PMF β) :
    IsCoupling (independentCoupling μ ν) μ ν := by
  constructor
  · simp [independentCoupling, PMF.map_bind, PMF.map_comp]
  · simp [independentCoupling, PMF.map_bind, PMF.map_comp, PMF.map_id]

theorem exists_coupling (μ : PMF α) (ν : PMF β) : ∃ π : PMF (α × β), IsCoupling π μ ν :=
  ⟨independentCoupling μ ν, isCoupling_independentCoupling μ ν⟩

/-- Expected cost of a coupling with respect to a cost function `c`. -/
noncomputable def couplingCost (π : PMF (α × β)) (c : α × β → ENNReal) : ENNReal :=
  ∑' z, π z * c z

/-- The Kantorovich optimal transport cost: infimum of `couplingCost` over all couplings. -/
noncomputable def kantorovichCost (μ : PMF α) (ν : PMF β) (c : α × β → ENNReal) : ENNReal :=
  sInf (Set.range (fun π : {π : PMF (α × β) // IsCoupling π μ ν} => couplingCost π.1 c))

theorem kantorovichCost_le_of_isCoupling (μ : PMF α) (ν : PMF β) (c : α × β → ENNReal)
    (π : PMF (α × β)) (hπ : IsCoupling π μ ν) :
    kantorovichCost μ ν c ≤ couplingCost π c := by
  unfold kantorovichCost
  refine sInf_le ?_
  exact ⟨⟨π, hπ⟩, rfl⟩

theorem kantorovichCost_le_independent (μ : PMF α) (ν : PMF β) (c : α × β → ENNReal) :
    kantorovichCost μ ν c ≤ couplingCost (independentCoupling μ ν) c :=
  kantorovichCost_le_of_isCoupling μ ν c (independentCoupling μ ν)
    (isCoupling_independentCoupling μ ν)

end Mettapedia.ProbabilityTheory.OptimalTransport

