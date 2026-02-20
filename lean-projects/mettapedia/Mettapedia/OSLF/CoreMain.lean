import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Types
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.FULLStatus
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.SynthesisBridge
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.LambdaInstance
import Mettapedia.OSLF.Framework.PetriNetInstance
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.MeTTaMinimalInstance
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.ObservationalQuotient
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.PLNSelectorGSLT
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.MeTTaCore.Premises
import Mettapedia.OSLF.MeTTaCore.FullLanguageDef
import Mettapedia.OSLF.Framework.MeTTaFullInstance
import Mettapedia.OSLF.Framework.MeTTaToNTT
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Decidability
import Mettapedia.OSLF.QuantifiedFormula
import Mettapedia.OSLF.QuantifiedFormula2
import Mettapedia.Logic.OSLFDistinctionGraph
import Mettapedia.Logic.OSLFDistinctionGraphWeighted
import Mettapedia.Logic.OSLFDistinctionGraphWM
import Mettapedia.Logic.OSLFDistinctionGraphEntropy
import Mettapedia.Logic.OSLFKripkeBridge
import Mettapedia.Logic.OSLFImageFinite
import Mettapedia.OSLF.Framework.PiRhoCanonicalBridge

/-!
# OSLF Core Entry Point

Sorry-free core entry point for OSLF + GSLT + premise-aware rewriting pipeline.

This file keeps the core stack and re-exports one canonical π→ρ pred-domain
endpoint for downstream OSLF consumers.
-/

namespace Mettapedia.OSLF

export Mettapedia.OSLF.MeTTaCore.Premises (
  space0Atomspace
  space0EqEntries
  space0TypeEntries
  space0Entries
  mkCanonicalSpace
  space0Pattern
  spaceEntriesOfPattern?
  atomspaceOfPattern?
  eqnLookupTuples
  noEqnLookupTuples
  neqTuples
  typeOfTuples
  notTypeOfTuples
  castTuples
  notCastTuples
  groundedCallTuples
  noGroundedCallTuples
)

export Mettapedia.OSLF.MeTTaCore.FullLanguageDef (
  mettaFull
  mettaFullOSLF
  mettaFullGalois
  mettaFullRelEnv
)

export Mettapedia.OSLF.Framework.MeTTaFullInstance (
  mettaFull_pathOrder
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaFullSpecAtomCheck
  mettaFullSpecAtomSem
  mettaFull_checkLangUsing_sat_sound_specAtoms
  mettaFull_checkLang_sat_sound_specAtoms
)

export Mettapedia.OSLF.Framework.MeTTaToNTT (
  mettaEvidenceToNT
  mettaEvidenceToNT_hom
  mettaSemE
  mettaSemE_atom
  mettaSemE_atom_revision
  mettaFormulaToNT
  mettaFormulaToNT_snd
  mettaFormulaToNT_atom
  mettaFormulaToNT_hom
)

export Mettapedia.OSLF.Framework.PiRhoCanonicalBridge (
  piRho_coreMain_canonical_contract_end_to_end
)

/-- CoreMain-facing canonical π→ρ semantic contract endpoint. -/
abbrev coreMain_piRho_canonical_contract :=
  @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_canonical_contract_end_to_end

/-- Canonical projection API for downstream users: consume the contract record
and project endpoint/HM capabilities directly. -/
theorem coreMain_piRho_contract_projection_api
    {N : Finset String}
    (x : Mettapedia.Languages.ProcessCalculi.PiCalculus.Name)
    (P : Mettapedia.Languages.ProcessCalculi.PiCalculus.Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (xr yr : Mettapedia.Languages.ProcessCalculi.PiCalculus.Name)
    (Pr : Mettapedia.Languages.ProcessCalculi.PiCalculus.Process)
    (n v : String)
    (hobs : N ⊆ P.freeNames)
    (hfresh : Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingFresh P) :
    Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.CalcPreludeLanguageMorphismSemanticTransferParamAtomPredDomain
      N x P nuListenerBody seedListenerBody xr yr Pr n v hfresh
    ∧
    (∃
      _ :
        Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
            Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreStarRel,
      True)
    ∧
    (∃
      _ :
        Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
            Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoDerivedStarRel,
      True)
    ∧
    (∀
      (S :
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.FiniteSubrelation
          Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreStarRel)
      (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq S.rel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar S.rel p q)
    ∧
    (∀ (I : Mettapedia.OSLF.Formula.AtomSem)
      {p q : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern},
      Mettapedia.Logic.OSLFKSUnificationSketch.OSLFObsEq
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel I p q →
      Mettapedia.Logic.OSLFKSUnificationSketch.Bisimilar
        Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.rhoCoreCanonicalRel p q) := by
  let C :=
    coreMain_piRho_canonical_contract
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v hobs hfresh
  exact ⟨C.endpoint, ⟨C.reachable_coreStar_subrel, trivial⟩,
    ⟨C.reachable_derivedStar_subrel, trivial⟩, C.hm_converse_coreStar_subrel,
    C.hm_converse_coreCanonical⟩

/-- CoreMain-facing canonical category/topos bridge endpoint alias. -/
abbrev coreMain_hypercube_fuzzy_bridge :=
  @Mettapedia.OSLF.Framework.CategoryBridge.hypercube_fuzzy_canonical_bridge

/-- CoreMain-facing canonical category/topos package endpoint. -/
theorem coreMain_category_topos_package
    {σ : Mettapedia.CategoryTheory.Hypercube.Slot →
        Mettapedia.CategoryTheory.Hypercube.HSort}
    (hσ : Mettapedia.CategoryTheory.Hypercube.isEquationallyAdmissible σ)
    (a b c : Mettapedia.CategoryTheory.FuzzyFrame.UnitInterval) :
    σ Mettapedia.CategoryTheory.Hypercube.Slot.result =
      Mettapedia.CategoryTheory.Hypercube.HSort.star ∧
      (a * b ≤ c ↔ b ≤ Mettapedia.CategoryTheory.FuzzyFrame.UnitInterval.productImp a c) ∧
      a * b ≤ a ⊓ b :=
  coreMain_hypercube_fuzzy_bridge hσ a b c

/-- Compatibility shim for downstream users of the pre-package endpoint name. -/
abbrev coreMain_fuzzy_product_residuation_bridge :=
  @Mettapedia.OSLF.Framework.CategoryBridge.fuzzy_product_residuation_bridge

/-- Compatibility shim for downstream users of the pre-package endpoint name. -/
abbrev coreMain_fuzzy_product_refines_meet_bridge :=
  @Mettapedia.OSLF.Framework.CategoryBridge.fuzzy_product_refines_meet_bridge

/-- Compatibility shim for downstream users of the pre-package endpoint name. -/
abbrev coreMain_hypercube_admissible_result_star_bridge :=
  @Mettapedia.OSLF.Framework.CategoryBridge.hypercube_admissible_result_star_bridge

/-- Compatibility shim for downstream users of the typed modal composition endpoint. -/
abbrev coreMain_hypercube_fuzzy_typed_modal_composition_bridge :=
  @Mettapedia.OSLF.Framework.CategoryBridge.hypercube_fuzzy_typed_modal_composition_bridge

#check Mettapedia.OSLF.Framework.FULLStatus.remaining_ne_nil
#check Mettapedia.OSLF.Framework.FULLStatus.remainingCount_pos
#check Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFull
#check Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFullOSLF
#check Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces
#check Mettapedia.Logic.OSLFImageFinite.hm_converse_langReduces
#check @Mettapedia.OSLF.Framework.PiRhoCanonicalBridge.piRho_coreMain_canonical_contract_end_to_end
#check @coreMain_piRho_canonical_contract
#check @coreMain_piRho_contract_projection_api
#check @coreMain_hypercube_fuzzy_bridge
#check @coreMain_hypercube_fuzzy_typed_modal_composition_bridge
#check @coreMain_category_topos_package

end Mettapedia.OSLF
