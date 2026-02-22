import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.NativeType.Construction

/-!
# Topos/Internal-Language and TOGL Graph Bridge Endpoints

Canonical packaged bridges that expose:

1. Presheaf-topos representable-fiber semantics together with conjunction/
   disjunction internalization.
2. Graph-theoretic reduction views (TOGL-style edge semantics) as equivalent
   presentations of OSLF `◇`/`□` semantics.
-/

namespace Mettapedia.OSLF.Framework.ToposTOGLBridge

open CategoryTheory
open Opposite
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine

universe u v

/-- Canonical package for the topos/internal-language route:
fiber-membership/satisfies equivalence, conjunction/disjunction internalization,
and graph-object characterizations of `◇` and `□` over the default relation
environment. -/
theorem topos_internal_language_bridge_package
    (lang : LanguageDef) (procSort : String := "Proc")
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Pattern) (φ ψ : Pattern → Prop)
    (hφ : Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality lang s seed φ)
    (hψ : Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality lang s seed ψ)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
    (h : (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s).obj X)
    (χ : Pattern → Prop) (p : Pattern) :
    (h ∈ (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang s seed φ hφ).obj X
      ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langOSLF lang procSort).satisfies
        (S := s.val) (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang h seed) φ)
    ∧
    (∃ hAnd hOr,
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_characteristicEquiv
          (lang := lang) (s := s))
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_characteristicMap
            lang s seed (fun t => φ t ∧ ψ t) hAnd)
        =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang s seed (fun t => φ t ∧ ψ t) hAnd
      ∧
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_characteristicEquiv
          (lang := lang) (s := s))
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_characteristicMap
            lang s seed (fun t => φ t ∨ ψ t) hOr)
        =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang s seed (fun t => φ t ∨ ψ t) hOr
      ∧
      (∀ {Y : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
          (k : (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s).obj Y),
          k ∈ (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang s seed (fun t => φ t ∧ ψ t) hAnd).obj Y
            ↔
            (φ (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k seed)
              ∧ ψ (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k seed)))
      ∧
      (∀ {Y : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
          (k : (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang s).obj Y),
          k ∈ (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang s seed (fun t => φ t ∨ ψ t) hOr).obj Y
            ↔
            (φ (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k seed)
              ∨ ψ (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k seed))))
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang χ p
      ↔
      ∃ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
            Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).source.app X e).down = p
          ∧
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).target.app X e).down))
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langBoxUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang χ p
      ↔
      ∀ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
            Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).target.app X e).down = p →
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).source.app X e).down)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_mem_iff_satisfies
        (lang := lang) (procSort := procSort)
        (s := s) (seed := seed) (φ := φ) (hNat := hφ) (h := h)
  · exact Mettapedia.OSLF.Framework.CategoryBridge.languageSort_conj_disj_topos_package
      lang s seed φ ψ hφ hψ
  · simpa using
      (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphObjStep
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
        (relEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
        (lang := lang)
        (G := Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang)
        (X := X) (φ := χ) (p := p))
  · simpa using
      (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphObjIncoming
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
        (relEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty)
        (lang := lang)
        (G := Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang)
        (X := X) (φ := χ) (p := p))

/-- Stronger topos/internal-language bridge theorem family:
packages the full presheaf-native restriction/equivalence assumptions/results
explicitly (via the scoped full-route package), together with the canonical
fiber/graph bridge facts. -/
theorem topos_internal_language_full_route_family
    (lang : LanguageDef) (procSort : String := "Proc")
    (A : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang)
    {B C : Mettapedia.OSLF.NativeType.ScopedConstructorPred lang}
    (f : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang A B)
    (g : Mettapedia.OSLF.NativeType.ScopedConstructorPredHom lang B C)
    (ψ : Pattern → Prop)
    (hψ : Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
      lang A.sort A.seed ψ)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
    (h : (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort).obj X)
    (χ : Pattern → Prop) (p : Pattern) :
    Mettapedia.OSLF.NativeType.FullRouteRestrictionEquivalence lang A
    ∧
    (Mettapedia.OSLF.NativeType.ScopedConstructorPredHom.comp f g).toFullGrothHom =
      Mettapedia.OSLF.NativeType.FullPresheafGrothendieckHom.comp
        f.toFullGrothHom g.toFullGrothHom
    ∧
    (h ∈ (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
      lang A.sort A.seed A.pred A.naturality).obj X
      ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langOSLF lang procSort).satisfies
        (S := A.sort.val) (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang h A.seed) A.pred)
    ∧
    (∃ hAnd hOr,
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_characteristicEquiv
          (lang := lang) (s := A.sort))
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_characteristicMap
            lang A.sort A.seed (fun t => A.pred t ∧ ψ t) hAnd)
        =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang A.sort A.seed (fun t => A.pred t ∧ ψ t) hAnd
      ∧
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_characteristicEquiv
          (lang := lang) (s := A.sort))
          (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_characteristicMap
            lang A.sort A.seed (fun t => A.pred t ∨ ψ t) hOr)
        =
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang A.sort A.seed (fun t => A.pred t ∨ ψ t) hOr
      ∧
      (∀ {Y : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
          (k : (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort).obj Y),
          k ∈ (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang A.sort A.seed (fun t => A.pred t ∧ ψ t) hAnd).obj Y
            ↔
            (A.pred (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k A.seed)
              ∧ ψ (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k A.seed)))
      ∧
      (∀ {Y : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
          (k : (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj lang A.sort).obj Y),
          k ∈ (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
            lang A.sort A.seed (fun t => A.pred t ∨ ψ t) hOr).obj Y
            ↔
            (A.pred (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k A.seed)
              ∨ ψ (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang k A.seed))))
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang χ p
      ↔
      ∃ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
            Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).source.app X e).down = p
          ∧
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).target.app X e).down))
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langBoxUsing
        Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang χ p
      ↔
      ∀ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
            Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).target.app X e).down = p →
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)
          Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang).source.app X e).down)) := by
  rcases Mettapedia.OSLF.NativeType.full_route_restriction_equivalence_package
      (A := A) f g with ⟨hRestr, hComp⟩
  rcases topos_internal_language_bridge_package
      (lang := lang) (procSort := procSort)
      (s := A.sort) (seed := A.seed)
      (φ := A.pred) (ψ := ψ)
      (hφ := A.naturality) (hψ := hψ)
      (X := X) h χ p with
    ⟨hMem, hConjDisj, hDia, hBox⟩
  exact ⟨hRestr, hComp, hMem, hConjDisj, hDia, hBox⟩

/-- Explicit TOGL-style graph bridge package:
operational `∃/∀` reduction characterizations are equivalent to edge-based
graph-object characterizations of `◇` and `□`. -/
theorem togl_graph_modal_bridge_package
    (lang : LanguageDef)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (C : Type u) [CategoryTheory.Category.{v} C]
    {X : Opposite C}
    (χ : Pattern → Prop) (p : Pattern) :
    ((∃ q, Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q ∧ χ q)
      ↔
      ∃ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).source.app X e).down = p
          ∧
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).target.app X e).down))
    ∧
    ((∀ q, Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q p → χ q)
      ↔
      ∀ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).target.app X e).down = p →
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).source.app X e).down)) := by
  refine ⟨?_, ?_⟩
  · exact
      (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing_spec relEnv lang χ p).symm.trans
        (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphObjStep
          (C := C) (relEnv := relEnv) (lang := lang)
          (G := Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang)
          (X := X) (φ := χ) (p := p))
  · exact
      (Mettapedia.OSLF.Framework.TypeSynthesis.langBoxUsing_spec relEnv lang χ p).symm.trans
        (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphObjIncoming
          (C := C) (relEnv := relEnv) (lang := lang)
          (G := Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang)
          (X := X) (φ := χ) (p := p))

/-- TOGL correspondence layer above graph-modal equivalence:
internal-subfunctor edge characterizations are equivalent to graph-object edge
characterizations for both `◇`-style and `□`-style views. -/
theorem togl_internal_graph_correspondence_layer
    (lang : LanguageDef)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (C : Type u) [CategoryTheory.Category.{v} C]
    {X : Opposite C}
    (χ : Pattern → Prop) (p : Pattern) :
    ((∃ q,
        (((ULift.up (p, q)) :
            (Mettapedia.OSLF.Framework.ToposReduction.pairConstPresheaf (C := C)).obj X) ∈
          (Mettapedia.OSLF.Framework.ToposReduction.reductionSubfunctorUsing
            (C := C) relEnv lang).obj X)
        ∧ χ q)
      ↔
      ∃ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).source.app X e).down = p
          ∧
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).target.app X e).down))
    ∧
    ((∀ q,
        (((ULift.up (q, p)) :
            (Mettapedia.OSLF.Framework.ToposReduction.pairConstPresheaf (C := C)).obj X) ∈
          (Mettapedia.OSLF.Framework.ToposReduction.reductionSubfunctorUsing
            (C := C) relEnv lang).obj X) →
        χ q)
      ↔
      ∀ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).target.app X e).down = p →
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).source.app X e).down)) := by
  have hGraph := togl_graph_modal_bridge_package (lang := lang) (relEnv := relEnv)
    (C := C) (X := X) χ p
  have hInternalToOperationalDia :
      (∃ q,
          (((ULift.up (p, q)) :
              (Mettapedia.OSLF.Framework.ToposReduction.pairConstPresheaf (C := C)).obj X) ∈
            (Mettapedia.OSLF.Framework.ToposReduction.reductionSubfunctorUsing
              (C := C) relEnv lang).obj X) ∧ χ q)
        ↔
      (∃ q, Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q ∧ χ q) := by
    exact
      (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_internalStep
        (C := C) (relEnv := relEnv) (lang := lang) (X := X) (φ := χ) (p := p)).symm.trans
        (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing_spec relEnv lang χ p)
  have hInternalToOperationalBox :
      (∀ q,
          (((ULift.up (q, p)) :
              (Mettapedia.OSLF.Framework.ToposReduction.pairConstPresheaf (C := C)).obj X) ∈
            (Mettapedia.OSLF.Framework.ToposReduction.reductionSubfunctorUsing
              (C := C) relEnv lang).obj X) →
          χ q)
        ↔
      (∀ q, Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q p → χ q) := by
    exact
      (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_internalStep
        (C := C) (relEnv := relEnv) (lang := lang) (X := X) (φ := χ) (p := p)).symm.trans
        (Mettapedia.OSLF.Framework.TypeSynthesis.langBoxUsing_spec relEnv lang χ p)
  exact ⟨hInternalToOperationalDia.trans hGraph.1, hInternalToOperationalBox.trans hGraph.2⟩

/-- TOGL graph-algebra theorem family tied directly to
`reductionGraphObjUsing` endpoints:
- edge endpoint relation as one-step reduction,
- `◇` as existence of an outgoing edge from `p`,
- `□` as a condition over incoming edges into `p`. -/
theorem togl_graph_algebra_reductionGraphObj_family
    (lang : LanguageDef)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (C : Type u) [CategoryTheory.Category.{v} C]
    {X : Opposite C}
    (χ : Pattern → Prop) (p q : Pattern) :
    ((∃ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).source.app X e).down = p
          ∧
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).target.app X e).down = q)
      ↔
      Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q)
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing relEnv lang χ p
      ↔
      ∃ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).source.app X e).down = p
          ∧
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).target.app X e).down))
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langBoxUsing relEnv lang χ p
      ↔
      ∀ e :
        (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).Edge.obj X,
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).target.app X e).down = p →
        χ (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
            (C := C) relEnv lang).source.app X e).down)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
        (C := C) relEnv lang).edge_endpoints_iff (X := X) (p := p) (q := q)
  · simpa using
      (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphObjStep
        (C := C) (relEnv := relEnv) (lang := lang)
        (G := Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang)
        (X := X) (φ := χ) (p := p))
  · simpa using
      (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphObjIncoming
        (C := C) (relEnv := relEnv) (lang := lang)
        (G := Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang)
        (X := X) (φ := χ) (p := p))

/-- TOGL-style two-edge composition shape in `reductionGraphObjUsing`. -/
def graphChain2
    (lang : LanguageDef)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (C : Type u) [CategoryTheory.Category.{v} C]
    {X : Opposite C}
    (p r : Pattern) : Prop :=
  ∃ e₁ e₂ :
      (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
        (C := C) relEnv lang).Edge.obj X,
    ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
      (C := C) relEnv lang).source.app X e₁).down = p
    ∧
    ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
      (C := C) relEnv lang).target.app X e₁).down =
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
        (C := C) relEnv lang).source.app X e₂).down
    ∧
    ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
      (C := C) relEnv lang).target.app X e₂).down = r

/-- TOGL family theorem connecting graph composition laws to
`reductionGraphObjUsing` endpoints:
two-edge graph composition is equivalent to relational composition of one-step
reductions. -/
theorem togl_graph_composition_reductionGraphObj_family
    (lang : LanguageDef)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (C : Type u) [CategoryTheory.Category.{v} C]
    {X : Opposite C}
    (p r : Pattern) :
    graphChain2 (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r
      ↔
    ∃ q,
      Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q
      ∧
      Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r := by
  constructor
  · rintro ⟨e₁, e₂, hs₁, hlink, ht₂⟩
    let q : Pattern :=
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
        (C := C) relEnv lang).target.app X e₁).down
    have hpq :
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang p q := by
      exact
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).edge_endpoints_iff
            (X := X) (p := p) (q := q)).1 ⟨e₁, hs₁, rfl⟩
    have hqr :
        Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang q r := by
      exact
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
          (C := C) relEnv lang).edge_endpoints_iff
            (X := X) (p := q) (q := r)).1
          ⟨e₂, by simpa [q] using hlink.symm, ht₂⟩
    exact ⟨q, hpq, hqr⟩
  · rintro ⟨q, hpq, hqr⟩
    rcases ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
      (C := C) relEnv lang).edge_endpoints_iff
        (X := X) (p := p) (q := q)).2 hpq with ⟨e₁, hs₁, ht₁⟩
    rcases ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphObjUsing
      (C := C) relEnv lang).edge_endpoints_iff
        (X := X) (p := q) (q := r)).2 hqr with ⟨e₂, hs₂, ht₂⟩
    exact ⟨e₁, e₂, hs₁, ht₁.trans hs₂.symm, ht₂⟩

/-- Modal two-step version of graph composition:
`◇◇χ` coincides with existence of a two-edge graph chain whose endpoint
satisfies `χ`. -/
theorem togl_graph_composition_diamond_family
    (lang : LanguageDef)
    (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (C : Type u) [CategoryTheory.Category.{v} C]
    {X : Opposite C}
    (χ : Pattern → Prop) (p : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing
      relEnv lang
      (fun q => Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing relEnv lang χ q) p
      ↔
    ∃ r, graphChain2 (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r ∧ χ r := by
  constructor
  · intro h
    rcases (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing_spec
      relEnv lang
      (fun q => Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing relEnv lang χ q)
      p).1 h with ⟨q, hpq, hDiaQ⟩
    rcases (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing_spec
      relEnv lang χ q).1 hDiaQ with ⟨r, hqr, hχ⟩
    have hChain :
        graphChain2 (lang := lang) (relEnv := relEnv) (C := C) (X := X) p r := by
      exact (togl_graph_composition_reductionGraphObj_family
        (lang := lang) (relEnv := relEnv) (C := C) (X := X) (p := p) (r := r)).2
        ⟨q, hpq, hqr⟩
    exact ⟨r, hChain, hχ⟩
  · rintro ⟨r, hChain, hχ⟩
    rcases (togl_graph_composition_reductionGraphObj_family
      (lang := lang) (relEnv := relEnv) (C := C) (X := X) (p := p) (r := r)).1 hChain with
      ⟨q, hpq, hqr⟩
    have hDiaQ :
        Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing relEnv lang χ q := by
      exact (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing_spec
        relEnv lang χ q).2 ⟨r, hqr, hχ⟩
    exact (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing_spec
      relEnv lang
      (fun q => Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing relEnv lang χ q)
      p).2 ⟨q, hpq, hDiaQ⟩

end Mettapedia.OSLF.Framework.ToposTOGLBridge
