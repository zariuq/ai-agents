import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.EvidenceQuantale

/-!
# PLN World Models (Posterior-State Interface)

This module defines a minimal interface for the **complete** (“distribution-passing”) PLN layer:

- A *world-model posterior state* `State` that can be revised by combining independent evidence
  sources (an `EvidenceType`, i.e. an additive commutative monoid).
- Query projections that extract **binary Evidence** (`n⁺, n⁻`) for arbitrary queries.

All truth-value notions (strength/weight/confidence/interval bounds) are **views** computed from
the extracted `Evidence`.  They are intentionally not part of the core interface.

This is the “WM judgment + query judgment” split:

- build/revise posterior states in `State`;
- answer queries by extracting evidence from the state.
-/

namespace Mettapedia.Logic.PLNWorldModel

open scoped ENNReal

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNEvidence

/-! ## Queries -/

/-- Standard PLN queries over a set of atoms: events/propositions and links/conditionals. -/
inductive PLNQuery (Atom : Type*) where
  /-- Evidence for an event/proposition. -/
  | prop : Atom → PLNQuery Atom
  /-- Evidence for a link/conditional. -/
  | link : Atom → Atom → PLNQuery Atom

/-! ## Interface -/

/-- A revisable posterior state supporting **additive** evidence-valued query extraction.

`State` is an `EvidenceType` (so revision is `+`), and queries extract `Evidence`.

The `evidence_add` law is the key commutation property:
extracting from revised states is the same as revising extracted evidence. -/
class WorldModel (State : Type*) (Query : Type*) [EvidenceType State] where
  /-- Extract binary evidence for a query. -/
  evidence : State → Query → Evidence
  /-- Extraction commutes with revision (`+`) in the world-model state. -/
  evidence_add : ∀ W₁ W₂ q, evidence (W₁ + W₂) q = evidence W₁ q + evidence W₂ q

namespace WorldModel

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

/-! ## Generic views (derived, not stored) -/

/-- Posterior-mean probability view of a query (improper-prior strength). -/
noncomputable def queryStrength (W : State) (q : Query) : ℝ≥0∞ :=
  Evidence.toStrength (WorldModel.evidence (State := State) (Query := Query) W q)

/-- WTV view for a query, using the canonical `Evidence → WTV` map with prior size `κ`.
This is operational plumbing; the core state remains `Evidence`. -/
noncomputable def queryWTV (κ : ℝ≥0∞) (W : State) (q : Query) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (WorldModel.evidence (State := State) (Query := Query) W q)

theorem evidence_add' (W₁ W₂ : State) (q : Query) :
    WorldModel.evidence (State := State) (Query := Query) (W₁ + W₂) q =
      WorldModel.evidence (State := State) (Query := Query) W₁ q +
        WorldModel.evidence (State := State) (Query := Query) W₂ q :=
  WorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ q

end WorldModel

/-! ## Standard prop/link wrappers (when `Query = PLNQuery Atom`) -/

namespace PLNQuery

variable {State Atom : Type*} [EvidenceType State] [WorldModel State (PLNQuery Atom)]

def propEvidence (W : State) (a : Atom) : Evidence :=
  WorldModel.evidence (State := State) (Query := PLNQuery Atom) W (.prop a)

def linkEvidence (W : State) (a b : Atom) : Evidence :=
  WorldModel.evidence (State := State) (Query := PLNQuery Atom) W (.link a b)

noncomputable def propStrength (W : State) (a : Atom) : ℝ≥0∞ :=
  Evidence.toStrength (propEvidence (State := State) (Atom := Atom) W a)

noncomputable def linkStrength (W : State) (a b : Atom) : ℝ≥0∞ :=
  Evidence.toStrength (linkEvidence (State := State) (Atom := Atom) W a b)

noncomputable def propWTV (κ : ℝ≥0∞) (W : State) (a : Atom) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (propEvidence (State := State) (Atom := Atom) W a)

noncomputable def linkWTV (κ : ℝ≥0∞) (W : State) (a b : Atom) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (linkEvidence (State := State) (Atom := Atom) W a b)

theorem propEvidence_add (W₁ W₂ : State) (a : Atom) :
    propEvidence (State := State) (Atom := Atom) (W₁ + W₂) a =
      propEvidence (State := State) (Atom := Atom) W₁ a +
        propEvidence (State := State) (Atom := Atom) W₂ a := by
  simpa [propEvidence] using WorldModel.evidence_add' (State := State) (Query := PLNQuery Atom) W₁ W₂
    (.prop a)

theorem linkEvidence_add (W₁ W₂ : State) (a b : Atom) :
    linkEvidence (State := State) (Atom := Atom) (W₁ + W₂) a b =
      linkEvidence (State := State) (Atom := Atom) W₁ a b +
        linkEvidence (State := State) (Atom := Atom) W₂ a b := by
  simpa [linkEvidence] using WorldModel.evidence_add' (State := State) (Query := PLNQuery Atom) W₁ W₂
    (.link a b)

end PLNQuery

end Mettapedia.Logic.PLNWorldModel
