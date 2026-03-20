import Mettapedia.Logic.WorldModelAdditive
import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.EvidenceClass

/-!
# Universal Ensemble World Model

For ANY type T and ANY evidence carrier Ev with `AddCommMonoid`, multisets
over T with an atomic contribution function give an `AdditiveWorldModel`.

This is the UNIVERSALITY result: you don't need to CHOOSE a world model.
Every typed rewrite system GENERATES one. The WM calculus isn't imposing
structure on the world; it's discovering structure that's already there.

## The Theorem

Given:
- `T : Type*` — any observation type
- `Ev : Type*` with `AddCommMonoid` — any evidence carrier
- `Query : Type*` — any query type
- `contribute : T → Query → Ev` — atomic evidence contribution

Then `Multiset T` with `genAdditiveExtension contribute` satisfies:
- `extract (σ₁ + σ₂) q = extract σ₁ q + extract σ₂ q` (additivity)
- `extract 0 q = 0` (zero)
- The extraction is an `AddMonoidHom` (the profile-hom)

## References

- `WorldModelAdditive.lean`: `genAdditiveExtension`, `genAdditiveExtensionProfileHom`
- `OSLF/Framework/GSLTWorldModel.lean`: `universalEnsembleWorldModel` (binary-specific)
- WM-PLN book, Ch 7: "multiset ensembles give a canonical world model"

0 sorry.
-/

namespace Mettapedia.Logic.UniversalEnsembleWM

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.PLNWorldModelAdditive

/-! ## 1. The universal additive world model

For any observation type, query type, and evidence carrier, multisets
of observations with an atomic contribution function form an
AdditiveWorldModel. The extraction is `genAdditiveExtension`. -/

variable {Obs Query Ev : Type*} [AddCommMonoid Ev]

/-- The universal extraction law: combining observation multisets then
    extracting equals extracting then combining evidence.

    This is `extract_add` — the defining property of AdditiveWorldModel —
    instantiated for the multiset ensemble. -/
theorem universalExtractAdd
    (contribute : GenAtomicEvidenceContribution Obs Query Ev)
    (σ₁ σ₂ : Multiset Obs) (q : Query) :
    genAdditiveExtension contribute (σ₁ + σ₂) q =
    genAdditiveExtension contribute σ₁ q + genAdditiveExtension contribute σ₂ q :=
  genAdditiveExtension_add contribute σ₁ σ₂ q

/-- The universal zero law: empty observations give zero evidence. -/
theorem universalExtractZero
    (contribute : GenAtomicEvidenceContribution Obs Query Ev) (q : Query) :
    genAdditiveExtension contribute (0 : Multiset Obs) q = 0 :=
  genAdditiveExtension_zero contribute q

/-- The universal profile homomorphism: extraction is an `AddMonoidHom`
    from `Multiset Obs` to evidence profiles `Query → Ev`.

    This is the profile-hom form of the universality result:
    multisets → profiles is a structure-preserving map. -/
noncomputable def universalProfileHom
    (contribute : GenAtomicEvidenceContribution Obs Query Ev) :
    AddMonoidHom (Multiset Obs) (Query → Ev) :=
  genAdditiveExtensionProfileHom contribute

/-- The profile hom maps multiset addition to pointwise evidence addition. -/
theorem universalProfileHom_add
    (contribute : GenAtomicEvidenceContribution Obs Query Ev)
    (σ₁ σ₂ : Multiset Obs) :
    universalProfileHom contribute (σ₁ + σ₂) =
    fun q => universalProfileHom contribute σ₁ q +
             universalProfileHom contribute σ₂ q := by
  exact (universalProfileHom contribute).map_add σ₁ σ₂

/-! ## 2. Universality: uniqueness

The additive extension is UNIQUE: any map that preserves 0, singletons,
and multiset addition equals `genAdditiveExtension`. -/

/-- Any additive extension equals the universal one.
    This is the uniqueness half of the universal property. -/
theorem universalUniqueness
    (contribute : GenAtomicEvidenceContribution Obs Query Ev)
    {E : Multiset Obs → Query → Ev}
    (hE : GenIsAdditiveExtension contribute E) :
    E = genAdditiveExtension contribute :=
  eq_genAdditiveExtension contribute hE

/-! ## 3. Summary: existence + uniqueness = universality -/

/-- The complete universality theorem: for any atomic contribution,
    there exists a UNIQUE additive extension, and it equals
    `genAdditiveExtension`. -/
theorem universalEnsembleTheorem
    (contribute : GenAtomicEvidenceContribution Obs Query Ev) :
    -- Existence: genAdditiveExtension IS an additive extension
    GenIsAdditiveExtension contribute (genAdditiveExtension contribute) ∧
    -- Uniqueness: any other additive extension equals it
    (∀ {E}, GenIsAdditiveExtension contribute E →
      E = genAdditiveExtension contribute) :=
  ⟨genIsAdditiveExtension_genAdditiveExtension contribute,
   fun hE => eq_genAdditiveExtension contribute hE⟩

end Mettapedia.Logic.UniversalEnsembleWM
