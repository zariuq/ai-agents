import Mathlib.Data.ENNReal.Real
import Mettapedia.Logic.PLNWorldModel

/-!
# Additive World-Model No-Go Theorems

This module records the first basic incompatibility theorem for additive world models:

- if state revision is idempotent (`W + W = W`),
- and extracted evidence is finite,
- then additive extraction forces that evidence to be zero.

This does **not** say that every additive world model is trivial. It isolates the exact
conflict between:

- additive accumulation of independent evidence, and
- globally idempotent revision at the state layer.

Positive example:
- multiset/bag-style evidence ledgers are additive and non-idempotent.

Negative example:
- a deduplicating/set-style merge cannot remain both additive and finitely nontrivial
  under the current `WorldModel.evidence_add` law.
-/

namespace Mettapedia.Logic.PLNWorldModelAdditiveNoGo

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

namespace EvidenceQuantale.Evidence

/-- Finite evidence excludes the `∞` idempotence corner case in `ℝ≥0∞`. -/
def IsFinite (e : Evidence) : Prop :=
  e.pos ≠ ⊤ ∧ e.neg ≠ ⊤

theorem finite_coord_add_idempotent_eq_zero
    {x : ℝ≥0∞} (hfin : x ≠ ⊤) (hidem : x + x = x) :
    x = 0 := by
  have htoReal : x.toReal + x.toReal = x.toReal := by
    rw [← ENNReal.toReal_add hfin hfin, hidem]
  have hzeroReal : x.toReal = 0 := by
    nlinarith
  rcases (ENNReal.toReal_eq_zero_iff x).mp hzeroReal with hx | hx
  · exact hx
  · exact False.elim (hfin hx)

theorem eq_zero_of_hplus_idempotent
    {e : Evidence} (hfin : EvidenceQuantale.Evidence.IsFinite e) (hidem : e + e = e) :
    e = 0 := by
  rcases hfin with ⟨hposFin, hnegFin⟩
  apply Evidence.ext'
  · have hpos : e.pos + e.pos = e.pos := by
      simpa [Evidence.hplus_def] using congrArg Evidence.pos hidem
    exact finite_coord_add_idempotent_eq_zero hposFin hpos
  · have hneg : e.neg + e.neg = e.neg := by
      simpa [Evidence.hplus_def] using congrArg Evidence.neg hidem
    exact finite_coord_add_idempotent_eq_zero hnegFin hneg

end EvidenceQuantale.Evidence

section WorldModel

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

/-- In an additive world model, an idempotent state revision law forces every
finite extracted evidence value to vanish. -/
theorem evidence_eq_zero_of_revision_idempotent
    (W : State) (q : Query)
    (hidem : W + W = W)
    (hfin : EvidenceQuantale.Evidence.IsFinite
      (WorldModel.evidence (State := State) (Query := Query) W q)) :
    WorldModel.evidence (State := State) (Query := Query) W q = 0 := by
  have hEvidenceIdem :
      WorldModel.evidence (State := State) (Query := Query) W q +
          WorldModel.evidence (State := State) (Query := Query) W q =
        WorldModel.evidence (State := State) (Query := Query) W q := by
    calc
      WorldModel.evidence (State := State) (Query := Query) W q +
          WorldModel.evidence (State := State) (Query := Query) W q
        = WorldModel.evidence (State := State) (Query := Query) (W + W) q := by
            simpa using
              (WorldModel.evidence_add' (State := State) (Query := Query) W W q).symm
      _ = WorldModel.evidence (State := State) (Query := Query) W q := by
            simp [hidem]
  exact EvidenceQuantale.Evidence.eq_zero_of_hplus_idempotent hfin hEvidenceIdem

/-- No additive world model with globally idempotent revision can exhibit nonzero
finite evidence on any query. -/
theorem not_exists_nonzero_finite_evidence_of_revision_idempotent
    (hidem : ∀ W : State, W + W = W) :
    ¬ ∃ (W : State) (q : Query),
        let e := WorldModel.evidence (State := State) (Query := Query) W q
        EvidenceQuantale.Evidence.IsFinite e ∧ e ≠ 0 := by
  intro hExists
  rcases hExists with ⟨W, q, hfin, hne⟩
  have hzero :
      WorldModel.evidence (State := State) (Query := Query) W q = 0 :=
    evidence_eq_zero_of_revision_idempotent
      (State := State) (Query := Query) W q (hidem W) hfin
  exact hne hzero

end WorldModel

end Mettapedia.Logic.PLNWorldModelAdditiveNoGo
