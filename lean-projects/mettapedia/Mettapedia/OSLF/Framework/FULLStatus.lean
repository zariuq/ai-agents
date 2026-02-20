import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.GSLT.Topos.PredicateFibration
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.Framework.AssumptionNecessity
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Decidability
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.MeTTaMinimalInstance
import Mettapedia.OSLF.Framework.MeTTaFullInstance
import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.OSLF.QuantifiedFormula

/-!
# OSLF FULL Status Tracker

Machine-readable tracker for what is already formalized versus what is still
missing for a full presheaf-topos/native-type-theory OSLF lift.

This module is intentionally concrete: every entry includes a code reference
string so status reports can link back to Lean artifacts directly.
-/

namespace Mettapedia.OSLF.Framework.FULLStatus

/-- Current completion state for a FULL-OSLF milestone. -/
inductive MilestoneStatus where
  | done
  | inProgress
  | missing
  deriving DecidableEq, Repr

/-- One traceability row in the FULL-OSLF tracker. -/
structure Milestone where
  area : String
  title : String
  status : MilestoneStatus
  codeRef : String
  note : String
  deriving Repr

/-- Central FULL-OSLF status table.

    `status = done` means the artifact is formalized in Lean.
    `status = inProgress` means interface/hook exists but full theorem is pending.
    `status = missing` means no complete implementation/theorem yet. -/
def tracker : List Milestone :=
  [ { area := "OSLF Core"
      title := "LanguageDef → RewriteSystem → OSLF pipeline"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/TypeSynthesis.lean: langOSLF"
      note := "Generic synthesis and automatic modal Galois connection are in place." }
  , { area := "Premise Semantics"
      title := "Premise-aware executable/declarative equivalence"
      status := .done
      codeRef := "Mettapedia/OSLF/MeTTaIL/DeclReducesWithPremises.lean: engineWithPremisesUsing_sound/complete"
      note := "Engine path with premises has soundness/completeness bridge." }
  , { area := "Canonical vs Extension Policy"
      title := "rhoCalc blocks set-context descent; rhoCalcSetExt enables it"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/TypeSynthesis.lean: rhoSetDropWitness_canonical_vs_setExt"
      note := "Policy is enforced at LanguageDef/langReduces via `congruenceCollections`; low-level `RhoCalculus.Reduction.Reduces` remains a shared superset relation." }
  , { area := "Category Lift"
      title := "Presheaf-primary default consumer path"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/CategoryBridge.lean: SortPresheafCategory, predFibration, oslf_fibration, predFibration_presheafSortApprox_agreement"
      note := "Consumer-facing defaults now target the Ω/subobject presheaf backend; sort-wise path is retained via explicit compatibility wrappers (`predFibrationSortApprox`, `oslf_fibrationSortApprox`) and connected by an explicit discrete-base agreement theorem." }
  , { area := "Category Lift"
      title := "Sort base no longer hard-coded to Discrete"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/CategoryBridge.lean: SortCategoryInterface, lambdaTheorySortInterface, typeSortsLambdaInterface, languagePresheafLambdaTheory, languageSortRepresentableObj"
      note := "Both interface-parametric base selection and a real language-dependent presheaf λ-theory lift are formalized." }
  , { area := "Category Lift"
      title := "Predication over interface-selected base category"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/CategoryBridge.lean: predFibrationUsing, oslf_fibrationUsing, typeSortsPredFibrationViaLambdaInterface, langOSLFFibrationUsing_presheafAgreement, CommDiPathSemLiftPkg, commDiPathSemLiftPkg_of_liftEq, commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order, commDiWitnessLifting_of_pathSemLiftPkg, languageSortPredNaturality_commDi_pathSemClosed_of_pkg, languageSortFiber_ofPatternPred_mem_iff_satisfies; Mettapedia/OSLF/Formula.lean: checkLangUsing_sat_sound_sort_fiber, checkLangUsing_sat_sound_sort_fiber_mem_iff"
      note := "Interface-selected predication is closed by generic representable-fiber bridges plus explicit package-instantiation policy (manual liftEq route vs automatic path/subst+order route); checker-facing `sat → satisfies` is available at arbitrary language sorts." }
  , { area := "Presheaf Topos"
      title := "Internal Ω/sieve-based subobject semantics"
      status := .done
      codeRef := "Mettapedia/GSLT/Topos/SubobjectClassifier.lean: presheafSubobjectRepresentableByOmega / presheafCategoryHasClassifierConstructive; Mettapedia/OSLF/Framework/CategoryBridge.lean: languagePresheafLambdaTheory, languageSortFiber_characteristicEquiv"
      note := "Constructive Ω/sieve classifier path is wired into OSLF bridge through concrete language-presheaf λ-theory objects and sort-fiber characteristic-map equivalence." }
  , { area := "Reduction-as-Subobject"
      title := "Internal reduction graph with premises in topos"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/ToposReduction.lean: reductionGraphObjUsing / reductionGraphUsing_edge_endpoints_iff / langDiamondUsing_iff_exists_graphObjStep / langBoxUsing_iff_forall_graphObjIncoming; Mettapedia/OSLF/Formula.lean: checkLangUsingWithPred_sat_sound_graphObj_dia / checkLangUsingWithPred_sat_sound_graphObj_box"
      note := "Premise-aware one-step reduction is packaged as a reusable graph object abstraction over presheaves, with endpoint/modal (`◇`,`□`) graph-object bridges and checker-facing soundness corollaries for both `.dia` and `.box` over `ReductionGraphObj`." }
  , { area := "Beck-Chevalley"
      title := "Full substitution square in lifted base"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/BeckChevalleyOSLF.lean: presheaf_beckChevalley_square_direct / representable_patternPred_beckChevalley / representable_commDi_patternPred_beckChevalley / representable_commDi_patternPred_beckChevalley_of_pathSemLiftPkg / representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg / commDi_diamond_graphObj_square_direct; Mettapedia/OSLF/Framework/TinyMLInstance.lean: tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph / tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq; Mettapedia/OSLF/Framework/MeTTaMinimalInstance.lean: mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph / mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq / mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto; Mettapedia/OSLF/Framework/MeTTaFullInstance.lean: mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph / mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto / mettaFull_checkLangUsing_sat_sound_specAtoms"
      note := "Lifted-base substitution square is consumed end-to-end through package-based COMM/path-semantics transport with concrete non-rho checker→fiber→PathSemClosed BC+graph theorems for TinyML, MeTTaMinimal, and MeTTaFull." }
  , { area := "GF Evidence Semantics"
      title := "GF → OSLF → Evidence pipeline with canonical interface"
      status := .done
      codeRef := "Mettapedia/Languages/GF/WorldModelSemantics.lean: GFSemantics / gfRGLSemantics / gfWMFormulaSemE"
      note := "Canonical GFSemantics record bundles atomQuery + lang + injective proof. Evidence and threshold semantics derived. Active-passive evidence transparency proved." }
  , { area := "GF Evidence Semantics"
      title := "Temporal tense bridge (past/present/future)"
      status := .done
      codeRef := "Mettapedia/Languages/GF/WorldModelSemantics.lean: langReduces_pastTense / gfWMFormulaSemE_pastTense_transparent / past_present_patterns_differ / temporal_irreducible / present_does_not_entail_past_sem"
      note := "Tense rewrites TPast→⊛temporal(cl,-1), TPres→⊛temporal(cl,0), TFut→⊛temporal(cl,1). Evidence transparency and structural separation proved." }
  , { area := "GF Evidence Semantics"
      title := "Presupposition as evidence tensor-gating"
      status := .done
      codeRef := "Mettapedia/Logic/OSLFEvidenceSemantics.lean: presupGatedSemE / presupGated_one_presup / presupGated_bot_presup; Mettapedia/Languages/GF/WorldModelSemantics.lean: definiteDescriptionEvidence / negation_preserves_definite_presup / conditional_filters_definite_presup"
      note := "Presupposition = tensor gating. Projection laws: negation preserves, conditional filters. Definite description bridge with existence presupposition." }
  , { area := "GF Evidence Semantics"
      title := "Quantified formulas with scope ambiguity"
      status := .done
      codeRef := "Mettapedia/OSLF/QuantifiedFormula.lean: QFormula / qsemE / iSup_iInf_le_iInf_iSup; Mettapedia/Languages/GF/WorldModelSemantics.lean: surfaceScopeReading / inverseScopeReading / inverse_scope_le_surface_scope_evidence"
      note := "QFormula extends OSLFFormula with ∀/∃. Environment-based semantics. Scope ordering: inverse (specific) ≤ surface (non-specific)." }
  , { area := "GF Evidence Semantics"
      title := "Anaphora as variable binding"
      status := .done
      codeRef := "Mettapedia/Languages/GF/WorldModelSemantics.lean: anaphoricDiscourse / nonAnaphoricDiscourse / iSup_inf_le_inf_iSup"
      note := "Coreference modeled via shared variable binding in QFormula. Anaphoric reading ≤ non-anaphoric (same entity is stronger than different entities)." }
  , { area := "Assumption Audit"
      title := "HM converse star wrappers are necessity-audited (global image-finite cannot be discharged)"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/PiRhoCanonicalBridge.lean: hm_converse_rhoCoreStarRel / hm_converse_rhoDerivedStarRel; Mettapedia/OSLF/Framework/AssumptionNecessity.lean: not_global_hImageFinite_rhoCoreStarRel / not_global_hImageFinite_rhoDerivedStarRel"
      note := "Star-level HM wrappers remain assumption-scoped by design, and explicit non-image-finiteness witnesses now prove why global `hImageFinite` cannot be removed for these relations." }
  , { area := "Assumption Audit"
      title := "Global dia/box assumption wrappers are necessity-audited against pred-domain defaults"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/LanguageMorphism.lean: sem_of_diaBoxFragment; Mettapedia/OSLF/Framework/PiRhoCanonicalBridge.lean: preserves_fragment_rf_param_predDomain; Mettapedia/OSLF/Framework/AssumptionNecessity.lean: counterexample_hAtomAll_for_global_diaBox_transfer / counterexample_hDiaTopAll_for_global_diaBox_transfer"
      note := "Pred-domain atom wrappers are the canonical default; retained global wrappers are now explicitly justified by concrete counterexamples showing `hAtomAll`/`hDiaTopAll` cannot be dropped in full generality." }
  , { area := "Assumption Audit"
      title := "COMM/pathSem lifting assumptions (`commDiWitnessLifting`) in generic BC transfer lemmas"
      status := .inProgress
      codeRef := "Mettapedia/OSLF/Framework/CategoryBridge.lean: commDiWitnessLifting* family; Mettapedia/OSLF/Framework/BeckChevalleyOSLF.lean: representable_commDi_*"
      note := "Package-based routes (`CommDiPathSemLiftPkg`) are available, but generic assumption-level lemmas remain exported without tracked necessity counterexamples proving these assumptions cannot be removed in full generality." }
  , { area := "Assumption Audit"
      title := "Assumption-necessity counterexample library for retained global hypotheses"
      status := .done
      codeRef := "Mettapedia/OSLF/Framework/AssumptionNecessity.lean"
      note := "Dedicated necessity/counterexample theorem family is now formalized for retained global assumptions (`hImageFinite`, `hAtomAll`, `hDiaTopAll`) used by broad wrappers." }
  , { area := "Literature Alignment"
      title := "Internal conjunction/disjunction completion in paper-level topos route"
      status := .missing
      codeRef := "/home/zar/claude/literature/Hyperon Study Materials/Rho and OSLF/oslf.pdf (\"Conjunction. TBD\" / \"Disjunction. TBD\")"
      note := "Source OSLF paper marks these as TBD. FULL tracker now records them explicitly as open rather than implicitly complete." }
  , { area := "Literature Alignment"
      title := "Theory-translation preservation of Π/Ω in Native Type route"
      status := .missing
      codeRef := "/home/zar/claude/literature/Hyperon Study Materials/Rho and OSLF/Native_Type_Theory.pdf (future-work discussion on preserving Π and Ω)"
      note := "No canonical endpoint theorem yet certifies translation conditions preserving Π/Ω across the theory-morphism layer." }
  ]

/-- Count milestones with a given status. -/
def countBy (s : MilestoneStatus) : Nat :=
  (tracker.filter (fun m => m.status = s)).length

/-- Remaining FULL-OSLF milestones (in-progress + missing). -/
def remaining : List Milestone :=
  tracker.filter (fun m => m.status ≠ .done)

/-- Number of remaining FULL-OSLF milestones (in-progress + missing). -/
def remainingCount : Nat :=
  remaining.length

/-- Sanity check: FULL tracker currently includes unresolved milestones. -/
theorem remaining_ne_nil : remaining ≠ [] := by
  decide

/-- Sanity check: the unresolved-milestone count is strictly positive. -/
theorem remainingCount_pos : 0 < remainingCount := by
  decide

/-! ## Code-Reference Anchors

These checks tie tracker statements to concrete constants in the codebase.
-/

#check @Mettapedia.OSLF.Framework.TypeSynthesis.langOSLF
#check @Mettapedia.OSLF.Framework.TypeSynthesis.rhoSetDropWitness_canonical_vs_setExt
#check @Mettapedia.OSLF.MeTTaIL.DeclReducesPremises.engineWithPremisesUsing_sound
#check @Mettapedia.OSLF.MeTTaIL.DeclReducesPremises.engineWithPremisesUsing_complete
#check @Mettapedia.OSLF.Framework.CategoryBridge.SortCategoryInterface
#check @Mettapedia.OSLF.Framework.CategoryBridge.SortPresheafCategory
#check @Mettapedia.OSLF.Framework.CategoryBridge.lambdaTheorySortInterface
#check @Mettapedia.OSLF.Framework.CategoryBridge.predFibrationUsing
#check @Mettapedia.OSLF.Framework.CategoryBridge.oslf_fibrationUsing
#check @Mettapedia.OSLF.Framework.CategoryBridge.predFibration
#check @Mettapedia.OSLF.Framework.CategoryBridge.oslf_fibration
#check @Mettapedia.OSLF.Framework.CategoryBridge.predFibrationSortApprox
#check @Mettapedia.OSLF.Framework.CategoryBridge.oslf_fibrationSortApprox
#check @Mettapedia.OSLF.Framework.CategoryBridge.predFibration_presheafSortApprox_agreement
#check @Mettapedia.OSLF.Framework.CategoryBridge.typeSortsOSLFFibrationUsing_presheafAgreement
#check @Mettapedia.OSLF.Framework.CategoryBridge.langOSLFFibrationUsing_presheafAgreement
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoLangOSLFFibrationUsing_presheafAgreement
#check @Mettapedia.OSLF.Framework.CategoryBridge.languagePresheafLambdaTheory
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiPred
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting
#check @Mettapedia.OSLF.Framework.CategoryBridge.PathSemClosedPred
#check @Mettapedia.OSLF.Framework.CategoryBridge.CommDiPathSemLiftPkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_liftEq
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiPathSemLiftPkg_of_pathSem_comm_subst_and_path_order
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLiftPkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed_of_pkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.rho_proc_pathSemLift_pkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.rho_proc_commDiWitnessLifting_of_pkg
#check @Mettapedia.OSLF.Framework.CategoryBridge.pathSem_commSubst
#check @Mettapedia.OSLF.Framework.CategoryBridge.pathSemClosedPred_closed
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemClosed
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality_commDi_pathSemClosed
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_lift
#check @Mettapedia.OSLF.Framework.CategoryBridge.commDiWitnessLifting_of_pathSemLift
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_subobject
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_characteristicMap
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_characteristicMap_spec
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_mem_iff
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_mem_iff_satisfies
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoProc_langOSLF_predicate_to_fiber_mem_iff
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber_mem_iff
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_characteristicEquiv
#check @Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredicateFibration
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoProcRepresentableObj
#check @Mettapedia.OSLF.Framework.CategoryBridge.rhoProcSortFiber_characteristicEquiv
#check @Mettapedia.GSLT.Topos.beckChevalleyCondition_presheafChangeOfBase
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.presheafPrimary_beckChevalley_transport
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_patternPred_beckChevalley
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_lifting
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_pathSemLift
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_pathSemClosed
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_patternPred_beckChevalley_of_pathSemLiftPkg
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_lifting
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemLift
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemClosed
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.representable_commDi_bc_and_graphDiamond_of_pathSemLiftPkg
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.rhoProc_commDi_bc_and_graphDiamond_of_pathSemLift_pkg
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.langDiamondUsing_graph_transport
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.langBoxUsing_graph_transport
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi_diamond_graph_step_iff
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi_diamond_graphObj_square
#check @Mettapedia.OSLF.Framework.BeckChevalleyOSLF.commDi_diamond_graphObj_square_direct
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionSubfunctorUsing
#check @Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing_edge_endpoints_iff
#check @Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphStep
#check @Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphIncoming
#check @Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphObjStep
#check @Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphObjIncoming
#check @Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_internalStep
#check @Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_internalStep
#check @Mettapedia.OSLF.Formula.checkLangUsing_sat_sound_sort_fiber
#check @Mettapedia.OSLF.Formula.checkLangUsing_sat_sound_sort_fiber_mem_iff
#check @Mettapedia.OSLF.Formula.checkLangUsing_sat_sound_proc_fiber_using
#check @Mettapedia.OSLF.Formula.checkLangUsing_sat_sound_proc_fiber_using_mem_iff
#check @Mettapedia.OSLF.Formula.checkLang_sat_sound_proc_fiber_using
#check @Mettapedia.OSLF.Formula.checkLangUsingWithPred_sat_sound_graphObj_dia
#check @Mettapedia.OSLF.Formula.checkLangUsingWithPred_sat_sound_graphObj_box
#check @Mettapedia.OSLF.Framework.TinyMLInstance.tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph
#check @Mettapedia.OSLF.Framework.TinyMLInstance.tinyML_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_commDiPathSemLiftPkg_of_liftEq
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_of_liftEq
#check @Mettapedia.OSLF.Framework.MeTTaMinimalInstance.mettaMinimal_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
#check @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
#check @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
#check @Mettapedia.OSLF.Framework.MeTTaFullInstance.mettaFull_checkLangUsing_sat_sound_specAtoms

-- GF Evidence Semantics pipeline
#check @Mettapedia.Languages.GF.WorldModelSemantics.GFSemantics
#check @Mettapedia.Languages.GF.WorldModelSemantics.gfRGLSemantics
#check @Mettapedia.Languages.GF.WorldModelSemantics.gfWMFormulaSemE
#check @Mettapedia.Languages.GF.WorldModelSemantics.gfWMFormulaSemE_activePassive_transparent
#check @Mettapedia.Languages.GF.WorldModelSemantics.langReduces_pastTense
#check @Mettapedia.Languages.GF.WorldModelSemantics.gfWMFormulaSemE_pastTense_transparent
#check @Mettapedia.Languages.GF.WorldModelSemantics.past_present_patterns_differ
#check @Mettapedia.Languages.GF.WorldModelSemantics.temporal_irreducible
#check @Mettapedia.Languages.GF.WorldModelSemantics.present_does_not_entail_past_sem
#check @Mettapedia.Languages.GF.WorldModelSemantics.definiteDescriptionEvidence
#check @Mettapedia.Languages.GF.WorldModelSemantics.negation_preserves_definite_presup
#check @Mettapedia.Languages.GF.WorldModelSemantics.conditional_filters_definite_presup
#check @Mettapedia.Languages.GF.WorldModelSemantics.inverse_scope_le_surface_scope_evidence
#check @Mettapedia.Languages.GF.WorldModelSemantics.iSup_inf_le_inf_iSup
-- Quantified formulas
#check @Mettapedia.OSLF.QuantifiedFormula.QFormula
#check @Mettapedia.OSLF.QuantifiedFormula.qsemE
#check @Mettapedia.OSLF.QuantifiedFormula.qsemE_forall_le
#check @Mettapedia.OSLF.QuantifiedFormula.qsemE_exists_le
#check @Mettapedia.OSLF.QuantifiedFormula.qsemE_forall_le_exists
#check @Mettapedia.OSLF.QuantifiedFormula.iSup_iInf_le_iInf_iSup
-- Presupposition layer
#check @Mettapedia.Logic.OSLFEvidenceSemantics.presupGatedSemE
#check @Mettapedia.Logic.OSLFEvidenceSemantics.presupGated_one_presup
#check @Mettapedia.Logic.OSLFEvidenceSemantics.presupGated_bot_presup
#check @Mettapedia.Logic.OSLFEvidenceSemantics.negation_preserves_presup
-- Temporal semantics
#check @Mettapedia.Logic.OSLFEvidenceSemantics.temporalPattern
#check @Mettapedia.Logic.OSLFEvidenceSemantics.lagLeadIdentity
#check @Mettapedia.Logic.OSLFEvidenceSemantics.predictiveImplication_mp
#check @Mettapedia.Logic.OSLFEvidenceSemantics.sequentialAnd_le_left

-- Decidability & reflection
#check @Mettapedia.OSLF.Formula.semFuel
#check @Mettapedia.OSLF.Formula.check_sat_iff_semFuel
#check @Mettapedia.OSLF.Formula.semFuel_implies_sem
#check @Mettapedia.OSLF.Formula.checker_not_complete_global
#check @Mettapedia.OSLF.Formula.checker_incomplete_box
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.rhoCoreStarRel_not_imageFinite
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.rhoDerivedStarRel_not_imageFinite
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.counterexample_hAtomAll_for_global_diaBox_transfer
#check @Mettapedia.OSLF.Framework.AssumptionNecessity.counterexample_hDiaTopAll_for_global_diaBox_transfer

end Mettapedia.OSLF.Framework.FULLStatus
