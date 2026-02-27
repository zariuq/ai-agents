import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.OSLF.Framework.LanguageMorphism
import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
import Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor
import Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics

/-!
# Quantale–Language Coherence

This module connects two transport layers:

1. **Pattern transport** along OSLF language morphisms / hypercube forward transport.
2. **Value transport** along quantale morphisms (`QuantaleHom.map_weakness`).

The key theorem packages both in one coherence bundle: sampled reachable states
transport along language morphisms, and weakness over sampled values commutes
with quantale transport.
-/

namespace Mettapedia.OSLF.Framework.QuantaleCoherence

open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
open Mettapedia.ProbabilityTheory.Hypercube

section WeaknessTransport

variable {Q Q' : Type*}
variable [Monoid Q] [CompleteLattice Q]
variable [Monoid Q'] [CompleteLattice Q']

/-- Weight-function view of sampled source patterns. -/
def sourceWeight {U : Type*} [Fintype U]
    (srcVal : Pattern → Q) (pick : U → Pattern) : WeightFunction U Q :=
  ⟨fun u => srcVal (pick u)⟩

/-- Weight-function view of sampled transported patterns. -/
def targetWeight {U : Type*} [Fintype U]
    (dstVal : Pattern → Q') (mapTerm : Pattern → Pattern) (pick : U → Pattern) :
    WeightFunction U Q' :=
  ⟨fun u => dstVal (mapTerm (pick u))⟩

/-- Weakness transport on sampled source patterns via `QuantaleHom`. -/
theorem map_weakness_sourceWeight
    {U : Type*} [Fintype U]
    (f : QuantaleHom Q Q')
    (srcVal : Pattern → Q) (pick : U → Pattern)
    (H : Finset (U × U)) :
    f (weakness (sourceWeight srcVal pick) H) =
      weakness
        (WeightFunction.map (U := U) (Q := Q) (Q' := Q') f (sourceWeight srcVal pick))
        H := by
  simpa using QuantaleHom.map_weakness
    (U := U) (Q := Q) (Q' := Q') (f := f)
    (wf := sourceWeight srcVal pick) (H := H)

/-- If destination values are pointwise the image of source values under `f`,
then sampled weakness commutes with transport. -/
theorem map_weakness_targetWeight
    {U : Type*} [Fintype U]
    (f : QuantaleHom Q Q')
    (mapTerm : Pattern → Pattern)
    (srcVal : Pattern → Q) (dstVal : Pattern → Q')
    (hVal : ∀ p, dstVal (mapTerm p) = f (srcVal p))
    (pick : U → Pattern)
    (H : Finset (U × U)) :
    f (weakness (sourceWeight srcVal pick) H) =
      weakness (targetWeight dstVal mapTerm pick) H := by
  calc
    f (weakness (sourceWeight srcVal pick) H)
        =
      weakness
        (WeightFunction.map (U := U) (Q := Q) (Q' := Q') f (sourceWeight srcVal pick))
        H := map_weakness_sourceWeight (U := U) f srcVal pick H
    _ = weakness (targetWeight dstVal mapTerm pick) H := by
      unfold weakness targetWeight sourceWeight
      simp [WeightFunction.map, hVal]

end WeaknessTransport

section LanguageTransport

variable {L₁ L₂ : LanguageDef}

/-- Single reachable state transport through a `LanguageMorphism` (Eq case). -/
theorem mapTerm_reachable_of_reachable
    (m : LanguageMorphism L₁ L₂ Eq)
    {p q : Pattern}
    (hReach : LangReducesStar L₁ p q) :
    LangReducesStar L₂ (m.mapTerm p) (m.mapTerm q) := by
  obtain ⟨T, hT, hEq⟩ := m.forward_multi_eq hReach
  simpa [hEq] using hT

end LanguageTransport

section CoherenceBundle

variable {L₁ L₂ : LanguageDef}
variable {Q Q' : Type*}
variable [Monoid Q] [CompleteLattice Q]
variable [Monoid Q'] [CompleteLattice Q']

/-- Main coherence theorem:
sampled reachability transports through `LanguageMorphism`,
and sampled weakness commutes through `QuantaleHom`. -/
theorem language_quantale_coherence_bundle
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom Q Q')
    (srcVal : Pattern → Q) (dstVal : Pattern → Q')
    (hVal : ∀ p, dstVal (m.mapTerm p) = f (srcVal p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U)) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness (sourceWeight srcVal pick) H) =
      weakness (targetWeight dstVal m.mapTerm pick) H := by
  refine ⟨?_, ?_⟩
  · intro u
    exact mapTerm_reachable_of_reachable m (hReach u)
  · exact map_weakness_targetWeight f m.mapTerm srcVal dstVal hVal pick H

/-- Atom-indexed corollary of `language_quantale_coherence_bundle`. -/
theorem language_quantale_coherence_bundle_atom
    (m : LanguageMorphism L₁ L₂ Eq)
    (f : QuantaleHom Q Q')
    (I : String → Pattern → Q)
    (J : String → Pattern → Q')
    (hAtom : ∀ a p, J a (m.mapTerm p) = f (I a p))
    (a : String)
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar L₁ p₀ (pick u))
    (H : Finset (U × U)) :
    (∀ u, LangReducesStar L₂ (m.mapTerm p₀) (m.mapTerm (pick u))) ∧
    f (weakness (sourceWeight (I a) pick) H) =
      weakness (targetWeight (J a) m.mapTerm pick) H := by
  exact language_quantale_coherence_bundle
    (m := m) (f := f) (srcVal := I a) (dstVal := J a)
    (hVal := hAtom a) (pick := pick) (hReach := hReach) (H := H)

end CoherenceBundle

section HypercubeSpecialization

/-- Hypercube specialization:
along `v ≤ w`, forward reduction transport and quantale weakness transport
commute as a single bundle (with `mapTerm = id`). -/
theorem hypercube_forward_quantale_coherence_bundle
    {v w : ProbabilityVertex}
    (hvw : v ≤ w)
    (f : QuantaleHom
      (QuantaleSemantics.semanticsOfVertex w).Q
      (QuantaleSemantics.semanticsOfVertex v).Q)
    (srcVal : Pattern → (QuantaleSemantics.semanticsOfVertex w).Q)
    (dstVal : Pattern → (QuantaleSemantics.semanticsOfVertex v).Q)
    (hVal : ∀ p, dstVal p = f (srcVal p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar
      (Mettapedia.OSLF.Framework.VertexRewriteRules.vertexLanguageDef w) p₀ (pick u))
    (H : Finset (U × U)) :
    (∀ u, LangReducesStar
      (Mettapedia.OSLF.Framework.VertexRewriteRules.vertexLanguageDef v) p₀ (pick u)) ∧
    f (weakness (sourceWeight srcVal pick) H) =
      weakness (targetWeight dstVal id pick) H := by
  refine ⟨?_, ?_⟩
  · intro u
    exact gslt_forward_transport hvw (hReach u)
  · exact map_weakness_targetWeight f id srcVal dstVal (by simpa using hVal) pick H

end HypercubeSpecialization

section HypercubeTemporalSpecialization

/-- Temporal/event hypercube specialization:
along `v ≤ w`, forward reduction transport for `vertexTemporalLanguageDef`
and quantale weakness transport commute as a single bundle (`mapTerm = id`). -/
theorem hypercube_forward_quantale_coherence_bundle_temporal
    {v w : ProbabilityVertex}
    (hvw : v ≤ w)
    (f : QuantaleHom
      (QuantaleSemantics.semanticsOfVertex w).Q
      (QuantaleSemantics.semanticsOfVertex v).Q)
    (srcVal : Pattern → (QuantaleSemantics.semanticsOfVertex w).Q)
    (dstVal : Pattern → (QuantaleSemantics.semanticsOfVertex v).Q)
    (hVal : ∀ p, dstVal p = f (srcVal p))
    {U : Type*} [Fintype U]
    (pick : U → Pattern) {p₀ : Pattern}
    (hReach : ∀ u, LangReducesStar
      (Mettapedia.OSLF.Framework.VertexTemporalRewriteRules.vertexTemporalLanguageDef w)
      p₀ (pick u))
    (H : Finset (U × U)) :
    (∀ u, LangReducesStar
      (Mettapedia.OSLF.Framework.VertexTemporalRewriteRules.vertexTemporalLanguageDef v)
      p₀ (pick u)) ∧
    f (weakness (sourceWeight srcVal pick) H) =
      weakness (targetWeight dstVal id pick) H := by
  refine ⟨?_, ?_⟩
  · intro u
    exact Mettapedia.OSLF.Framework.HypercubeTemporalGSLTFunctor.gslt_temporal_forward_transport
      hvw (hReach u)
  · exact map_weakness_targetWeight f id srcVal dstVal (by simpa using hVal) pick H

end HypercubeTemporalSpecialization

end Mettapedia.OSLF.Framework.QuantaleCoherence
