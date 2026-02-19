import Mettapedia.CategoryTheory.DeFinettiPerNDiagram
import Mettapedia.CategoryTheory.DeFinettiGlobalFinitaryDiagram
import Mettapedia.CategoryTheory.DeFinettiKleisliGirySkeleton
import Mettapedia.CategoryTheory.DeFinettiSequenceKernelCone
import Mettapedia.CategoryTheory.DeFinettiMarkovCategoryBridge

/-!
# Stable Export Surface for Categorical de Finetti

This file is an internal stable alias layer.
Downstream modules should prefer importing
`Mettapedia.CategoryTheory.DeFinettiExports`.

This module re-exports the stable theorem chain by providing lightweight alias
theorems.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.ProbabilityTheory.HigherOrderProbability

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Stable alias: unique latent mediator at measure level. -/
theorem deFinettiStable_existsUnique_latentThetaMeasure_of_exchangeable
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hX : ∀ i : ℕ, Measurable (X i))
    (hexch : Mettapedia.Logic.Exchangeability.InfiniteExchangeable X μ) :
    ∃! ν : Measure DeFinettiConnection.Theta, RepresentsLatentTheta X μ ν :=
  deFinetti_limitCone_universalMediator_latentTheta X μ hX hexch

/-- Stable export: global finitary-permutation lifted commutation is equivalent
to `IsPrefixLawCone`. -/
theorem deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    IsPrefixLawCone (Ω := Ω) X μ ↔
      GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ :=
  isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes (Ω := Ω) X μ

/-- Stable export: one-hop bridge from global-lifted commutation to cross-`n`
mediator uniqueness packaging. -/
theorem deFinettiStable_globalLiftedPrefixLawConeCommutes_to_crossNPackage
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hglobal : GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ) :
    Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) := by
  refine ⟨exchangeableCrossNLimitPackage_of_isPrefixLawCone
    (Ω := Ω) X μ ?_⟩
  exact (deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
    (Ω := Ω) X μ).2 hglobal

/-- Stable export: for a fixed law `μ`, global finitary lifted commutation is
equivalent to having both:
1. the prefix-law cone predicate, and
2. a concrete cross-`n` mediator package witness. -/
theorem deFinettiStable_globalLiftedPrefixLawConeCommutes_iff_prefixCone_and_crossNPackage
    (X : ℕ → Ω → Bool) (μ : Measure Ω) :
    GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ ↔
      (IsPrefixLawCone (Ω := Ω) X μ ∧
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ)) := by
  constructor
  · intro hglobal
    refine ⟨?_, ?_⟩
    · exact (deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
        (Ω := Ω) X μ).2 hglobal
    · exact deFinettiStable_globalLiftedPrefixLawConeCommutes_to_crossNPackage
        (Ω := Ω) X μ hglobal
  · intro h
    exact (deFinettiStable_isPrefixLawCone_iff_globalLiftedPrefixLawConeCommutes
      (Ω := Ω) X μ).1 h.1

/-- Stable export: true global Kleisli(Giry) `IsLimit` packaging is equivalent
to the global mediator uniqueness property for an iid-cone skeleton. -/
theorem deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique
    (cone : KleisliGiryIIDConeSkeleton) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUnique cone :=
  isLimit_iff_globalIIDConeMediatorUnique cone

/-- Stable export: any true `IsLimit` witness implies the Markov-only
mediator-uniqueness property for the same cone. -/
theorem deFinettiStable_isLimit_implies_globalIIDConeMediatorUnique_markovOnly
    (cone : KleisliGiryIIDConeSkeleton)
    (hlim : CategoryTheory.Limits.IsLimit (cone.toCone)) :
    GlobalIIDConeMediatorUnique_markovOnly cone :=
  isLimit_implies_globalIIDConeMediatorUnique_markovOnly cone hlim

/-- Stable export: canonical all-sources strengthening of the kernel universal
mediator API. -/
theorem deFinettiStable_kernelUniversalMediator_allSources_default
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator_allSources (Ω := Ω) X :=
  kernelLatentThetaUniversalMediator_allSources_default (Ω := Ω) X

/-- Stable export: on discrete source measurable spaces, the default qualitative
all-sources witness upgrades to a measurable latent kernel mediator. -/
theorem deFinettiStable_allSourcesKernel_discrete_of_allSourcesDefault
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (Y : Type) [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ]
    (hκexch : KernelExchangeable (X := coordProcess) κ) :
    ∃! L : ProbabilityTheory.Kernel Y LatentTheta,
      KernelRepresentsLatentTheta (X := coordProcess) (κ := κ) (fun y => L y) :=
  allSourcesKernel_discrete_of_allSourcesDefault
    (hunivDefault := hunivDefault) Y κ hκexch

/-- Stable export: all-sources Markov-only Kleisli mediator property implies
Markov-only global mediator uniqueness for the `iidSequenceKernelTheta` cone. -/
theorem deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_markovOnly (iidSequenceKleisliConeSkeleton hcommutes) :=
  globalIIDConeMediatorUnique_markovOnly_of_allSourcesKleisli
    (hcommutes := hcommutes) huniv

/-- Stable export: unrestricted all-sources Kleisli mediator property implies
full global mediator uniqueness for the `iidSequenceKernelTheta` cone. -/
theorem deFinettiStable_globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  globalIIDConeMediatorUnique_of_allSourcesKleisli_unrestricted
    (hcommutes := hcommutes) huniv

/-- Stable export (converse direction): full global mediator uniqueness for the
canonical `iidSequenceKernelTheta` cone implies unrestricted all-sources
Kleisli universality. -/
theorem deFinettiStable_allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (hmed : GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  allSourcesKleisli_unrestricted_of_globalIIDConeMediatorUnique
    (hcommutes := hcommutes) hmed

/-- Stable export: unrestricted all-sources Kleisli universality is equivalent
to full global mediator uniqueness for the canonical `iidSequenceKernelTheta`
cone. -/
theorem deFinettiStable_allSourcesKleisli_unrestricted_iff_globalIIDConeMediatorUnique
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  allSourcesKleisli_unrestricted_iff_globalIIDConeMediatorUnique
    (hcommutes := hcommutes)

/-- Stable export: unrestricted all-sources kernel-level factorization implies
unrestricted all-sources Kleisli universality. -/
theorem deFinettiStable_allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted :=
  allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted huniv

/-- Stable export: unrestricted all-sources Kleisli mediator property yields a
concrete `IsLimit` witness for the `iidSequenceKernelTheta` cone. -/
theorem deFinettiStable_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta)
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) :=
  deFinetti_iidSequenceKleisliCone_isLimit_of_allSourcesKleisli_unrestricted
    (hcommutes := hcommutes) huniv

/-- Stable export: one-hop Markov-only route for the canonical
`iidSequenceKernelTheta` cone: global finitary invariance plus all-sources
Markov-only Kleisli universality implies Markov-only global mediator
uniqueness. -/
theorem deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_allSourcesKleisli
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_allSourcesKleisli
    (hglobal := hglobal) huniv

/-- Stable export: one-hop unrestricted route for the canonical
`iidSequenceKernelTheta` cone: global finitary invariance plus unrestricted
all-sources Kleisli universality implies full global mediator uniqueness. -/
theorem deFinettiStable_globalIIDConeMediatorUnique_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    GlobalIIDConeMediatorUnique
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  globalIIDConeMediatorUnique_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (hglobal := hglobal) huniv

/-- Stable export: one-hop full-target `IsLimit` packaging for the canonical
`iidSequenceKernelTheta` cone from global finitary invariance and unrestricted
all-sources Kleisli universality. -/
theorem deFinettiStable_iidSequenceKleisliCone_isLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) :=
  deFinetti_iidSequenceKleisliCone_isLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (hglobal := hglobal) huniv

/-- Stable bridge: all-sources kernel-level factorization implies all-sources
Markov-only Kleisli universality. -/
theorem deFinettiStable_allSourcesKleisli_markovOnly_of_allSourcesKernelFactorization
    (huniv : KernelLatentThetaUniversalMediator_allSourcesFactorization) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly :=
  allSourcesKleisli_markovOnly_of_allSourcesKernelFactorization huniv

/-- Stable bridge: strict iid prefix law + all-sources kernel-level latent
mediation imply all-sources Markov-only Kleisli universality directly. -/
theorem deFinettiStable_allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel) :
    KernelLatentThetaUniversalMediator_allSourcesKleisli_markovOnly :=
  allSourcesKleisli_markovOnly_of_allSourcesKernel_and_prefixLaw
    (hprefix := hprefix) huniv

/-- Stable canonical Markov-only one-hop route (no commutes⇒Markov adapter):
global finitary invariance + Dirac latent witness + default all-sources
qualitative de Finetti imply Markov-only global mediator uniqueness for the
canonical `iidSequenceKernelTheta` cone. -/
theorem deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_allSourcesKleisli
    (hglobal := hglobal)
    (allSourcesKleisli_markovOnly_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
      (hglobal := hglobal)
      (hrepDirac := hrepDirac)
      (hunivDefault := hunivDefault))

/-- Stable one-hop route from all-sources kernel-level factorization:
combined with global finitary invariance of `iidSequenceKernelTheta`, it yields
Markov-only global mediator uniqueness for the canonical cone. -/
theorem deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_allSourcesKernelFactorization
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesFactorization) :
    GlobalIIDConeMediatorUnique_markovOnly
      (iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)) :=
  deFinettiStable_globalIIDConeMediatorUnique_markovOnly_of_globalFinitaryInvariance_and_allSourcesKleisli
    (hglobal := hglobal)
    (deFinettiStable_allSourcesKleisli_markovOnly_of_allSourcesKernelFactorization huniv)

/-- Stable export: specialized `P Bool` form of the true global Kleisli(Giry)
`IsLimit` equivalence. -/
theorem deFinettiStable_isLimit_iff_globalIIDConeMediatorUniqueProbBool
    (cone : KleisliGiryProbBoolIIDCone) :
    Nonempty (CategoryTheory.Limits.IsLimit (cone.toCone)) ↔
      GlobalIIDConeMediatorUniqueProbBool cone :=
  isLimit_iff_globalIIDConeMediatorUniqueProbBool cone

/-- Stable export: horizon-`n` cylinder evaluation for `iidSequenceKernelTheta`,
assuming the canonical Dirac latent mediator interface. -/
theorem deFinettiStable_iidSequenceKernelTheta_prefix_apply_of_latentDirac
    (hrep :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool) :
    iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) :=
  iidSequenceKernelTheta_prefix_apply_of_latentDirac hrep θ n xs

/-- Stable export: for the cone built from `iidSequenceKernelTheta`, true
`IsLimit` is equivalent to global mediator uniqueness. -/
theorem deFinettiStable_isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta
    (hcommutes : ∀ τ : FinSuppPermNat,
      CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
        iidSequenceKleisliHomTheta) :
    Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
      GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes) :=
  isLimit_iff_globalIIDConeMediatorUnique_iidSequenceKernelTheta hcommutes

/-- Stable export: no-extra-hypothesis (beyond global finitary invariance)
IsLimit-ready bundle for `iidSequenceKernelTheta`. -/
theorem deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :=
  iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance hglobal

/-- Stable export: concrete `IsLimit` witness for the global Kleisli(Giry)
cone built from `iidSequenceKernelTheta`, assuming:
1. global finitary invariance, and
2. global mediator uniqueness for the induced cone. -/
theorem deFinettiStable_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmed :
      GlobalIIDConeMediatorUnique
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal))) :
    Nonempty
      (CategoryTheory.Limits.IsLimit
        ((iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    ⟨(iidSequenceKleisliConeSkeleton
        (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).isLimitOfMediatorUnique
      hmed⟩

/-- Stable export (Path-B): if finite-prefix marginals of `iidSequenceKernelTheta`
match Bernoulli product marginals, then the full Kleisli(Giry) IsLimit-ready
bundle follows in one hop. -/
theorem deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ),
        (iidSequenceKernelTheta θ).map (seqPrefixProj n) =
          Measure.pi (fun _ : Fin n => thetaBernoulliKernel θ)) :
    ∃ hcommutes : ∀ τ : FinSuppPermNat,
        CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
          iidSequenceKleisliHomTheta,
      (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
            (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance
              (iidSequenceKernelTheta_globalFinitaryInvariance_of_iidProduct_bridge
                (iidSequenceKernelTheta_eq_iidProduct_of_prefix_pi_marginals hprefix)) θ)) ∧
      (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
        GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes)) :=
  iidSequenceKernelTheta_isLimitReady_of_prefix_pi_marginals hprefix

/-- Stable export: true limit cone for the per-`n` permutation diagram. -/
def deFinettiStable_perNPrefixDiagramLimitCone (n : ℕ) :
    CategoryTheory.Limits.LimitCone (perNPrefixDiagramFunctor n) :=
  perNPrefixDiagramLimitCone n

/-- Stable export: `HasLimit` packaging for the true per-`n` diagram. -/
theorem deFinettiStable_hasLimit_perNPrefixDiagramFunctor (n : ℕ) :
    CategoryTheory.Limits.HasLimit (perNPrefixDiagramFunctor n) :=
  hasLimit_perNPrefixDiagramFunctor n

/-- Stable export: single rewrite bridge connecting kernel-level universal
mediator API to per-`n` limit-mediator uniqueness packaging. -/
theorem deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ExchangeablePerNLimitMediatorUnique (Ω := Ω) X :=
  kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique (Y := Y) (Ω := Ω) X

/-- Stable export: one-hop bridge from kernel-level universal mediator API to the
global cross-`n` package family. -/
theorem deFinettiStable_kernelLatentThetaUniversalMediator_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  kernelLatentThetaUniversalMediator_iff_crossNPackageFamily (Y := Y) (Ω := Ω) X

/-- Stable export: full practical qualitative chain in one theorem.
This packages:
1. kernel-level universal mediator API,
2. per-`n` mediator uniqueness package,
3. global lifted commutation → cross-`n` package witnesses. -/
theorem deFinettiStable_kernelUniversalMediator_endToEnd_globalChain
    (X : ℕ → Ω → Bool) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ↔
      (ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ∧
        (∀ μ : Measure Ω, GlobalLiftedPrefixLawConeCommutes (Ω := Ω) X μ →
          Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ))) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact
        (deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
          (Y := Y) (Ω := Ω) X).1 h
    · intro μ hglobal
      exact deFinettiStable_globalLiftedPrefixLawConeCommutes_to_crossNPackage
        (Ω := Ω) X μ hglobal
  · intro h
    exact
      (deFinettiStable_kernelLatentThetaUniversalMediator_iff_perNLimitMediatorUnique
        (Y := Y) (Ω := Ω) X).2 h.1

/-- Stable export: Markov-core universal mediation plus global finitary
invariance gives the practical Kleisli(Giry) `IsLimit`-ready route. -/
theorem deFinettiStable_markovCore_to_kleisliRoute
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ)) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      (∃ hcommutes : ∀ τ : FinSuppPermNat,
          CategoryTheory.CategoryStruct.comp iidSequenceKleisliHomTheta (finSuppPermKleisliHom τ) =
            iidSequenceKleisliHomTheta,
        (∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
          iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
            ∫⁻ θ' : LatentTheta, (iidPrefixKernel n θ') ({xs} : Set (Fin n → Bool)) ∂
              (iidSequenceKernelTheta_canonicalLatentKernel_of_globalFinitaryInvariance hglobal θ)) ∧
        (Nonempty (CategoryTheory.Limits.IsLimit ((iidSequenceKleisliConeSkeleton hcommutes).toCone)) ↔
          GlobalIIDConeMediatorUnique (iidSequenceKleisliConeSkeleton hcommutes))) := by
  refine ⟨?_, ?_⟩
  · exact
      (kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
        (Y := Y) (Ω := Ω) X).1 hcore
  · exact
      deFinettiStable_iidSequenceKernelTheta_isLimitReady_of_globalFinitaryInvariance
        hglobal

/-- Stable export: Markov-core universal mediation plus global finitary
invariance and mediator uniqueness yield a concrete global Kleisli(Giry)
`IsLimit` witness for the `iidSequenceKernelTheta` cone. -/
theorem deFinettiStable_markovCore_to_kleisliIsLimit
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hmed :
      GlobalIIDConeMediatorUnique
        (iidSequenceKleisliConeSkeleton
          (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal))) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  refine ⟨?_, ?_⟩
  · exact
      (kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
        (Y := Y) (Ω := Ω) X).1 hcore
  · exact
      deFinettiStable_iidSequenceKernelTheta_hasIsLimit_of_globalFinitaryInvariance_and_mediatorUnique
        (hglobal := hglobal) hmed

/-- Stable export: Markov-core universal mediation plus global finitary
invariance and unrestricted all-sources Kleisli universality yield a concrete
global Kleisli(Giry) `IsLimit` witness for the `iidSequenceKernelTheta` cone,
without a separate mediator-uniqueness hypothesis. -/
theorem deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKleisli_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  refine ⟨?_, ?_⟩
  · exact
      (kernelLatentThetaUniversalMediatorInMarkovCore_iff_kernelLatentThetaUniversalMediator
        (Y := Y) (Ω := Ω) X).1 hcore
  · exact
      deFinettiStable_iidSequenceKleisliCone_isLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
        (hglobal := hglobal) huniv

/-- Stable export: same full-target route as above, but consuming an
unrestricted all-sources kernel-level factorization witness directly. -/
theorem deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernelFactorization_unrestricted
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (huniv :
      KernelLatentThetaUniversalMediator_allSourcesKernelFactorization_unrestricted) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal
      (deFinettiStable_allSourcesKleisli_unrestricted_of_allSourcesKernelFactorization_unrestricted
        huniv)

/-- Stable export: full-target route composed from kernel-level ingredients.
Given global finitary invariance, iid-prefix cylinder law for
`iidSequenceKernelTheta`, all-sources kernel-level mediator witnesses, and a
commutation-to-Markov bridge for source kernels, derive the concrete global
Kleisli(Giry) `IsLimit` witness with no separate mediator-uniqueness input. -/
theorem deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKernel_and_prefixLaw
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (huniv : KernelLatentThetaUniversalMediator_allSourcesKernel)
    (hmarkov_of_commutes :
      ∀ (Y : Type) [MeasurableSpace Y]
        (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq),
        (∀ τ : FinSuppPermNat,
          CategoryTheory.CategoryStruct.comp
              (kernelToKleisliHom
                (A := (MeasCat.of Y : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
              (finSuppPermKleisliHom τ) =
            kernelToKleisliHom
              (A := (MeasCat.of Y : KleisliGiry)) (B := KleisliBinarySeqObj) κ) →
          ProbabilityTheory.IsMarkovKernel κ) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal
      (allSourcesKleisli_unrestricted_of_allSourcesKernel_and_prefixLaw
        (hprefix := hprefix) (huniv := huniv)
        (hmarkov_of_commutes := hmarkov_of_commutes))

/-- Stable export: canonical one-hop route from default all-sources qualitative
de Finetti to the full Kleisli(Giry) `IsLimit` endpoint, using the built-in
latent-moment measurable embedding infrastructure (no extra Borel/embedding
assumptions at call sites). -/
theorem deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes :
      ∀ (Y : Type) [MeasurableSpace Y]
        (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq),
        (∀ τ : FinSuppPermNat,
          CategoryTheory.CategoryStruct.comp
              (kernelToKleisliHom
                (A := (MeasCat.of Y : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
              (finSuppPermKleisliHom τ) =
            kernelToKleisliHom
              (A := (MeasCat.of Y : KleisliGiry)) (B := KleisliBinarySeqObj) κ) →
          ProbabilityTheory.IsMarkovKernel κ) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_allSourcesKleisli_unrestricted
      (Y := Y) (Ω := Ω) X hcore hglobal
      (allSourcesKleisli_unrestricted_of_defaultAllSourcesKernel_and_globalFinitaryInvariance_and_latentDirac_of_canonicalMomentEmbedding
        (hglobal := hglobal)
        (hrepDirac := hrepDirac)
        (hunivDefault := hunivDefault)
        (hmarkov_of_commutes := hmarkov_of_commutes))

/-- Stable export: compatibility wrapper retaining the explicit strict prefix-law
input. Prefer the latent-Dirac route above. -/
theorem deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_prefixLaw
    (X : ℕ → Ω → Bool)
    (hcore : KernelLatentThetaUniversalMediatorInMarkovCore (Y := Y) (Ω := Ω) X)
    (hglobal : ∀ θ : LatentTheta, GlobalFinitarySeqConeCommutes (iidSequenceKernelTheta θ))
    (hprefix :
      ∀ (θ : LatentTheta) (n : ℕ) (xs : Fin n → Bool),
        iidSequenceKernelTheta θ (seqPrefixEvent n xs) =
          (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)))
    (hunivDefault :
      ∀ (Y' : Type) [MeasurableSpace Y'],
        KernelLatentThetaUniversalMediator (Y := Y') (Ω := GlobalBinarySeq) coordProcess)
    (hmarkov_of_commutes :
      ∀ (Y : Type) [MeasurableSpace Y]
        (κ : ProbabilityTheory.Kernel Y GlobalBinarySeq),
        (∀ τ : FinSuppPermNat,
          CategoryTheory.CategoryStruct.comp
              (kernelToKleisliHom
                (A := (MeasCat.of Y : KleisliGiry)) (B := KleisliBinarySeqObj) κ)
              (finSuppPermKleisliHom τ) =
            kernelToKleisliHom
              (A := (MeasCat.of Y : KleisliGiry)) (B := KleisliBinarySeqObj) κ) →
          ProbabilityTheory.IsMarkovKernel κ) :
    KernelLatentThetaUniversalMediator (Y := Y) (Ω := Ω) X ∧
      Nonempty
        (CategoryTheory.Limits.IsLimit
          ((iidSequenceKleisliConeSkeleton
            (iidSequenceKleisliHomTheta_commutes_of_globalFinitaryInvariance hglobal)).toCone)) := by
  have hrepDirac :
      KernelRepresentsLatentTheta
        (Y := LatentTheta) (Ω := GlobalBinarySeq) (X := coordProcess)
        (κ := iidSequenceKernelTheta)
        (fun θ : LatentTheta => (Measure.dirac θ : Measure LatentTheta)) :=
    iidSequenceKernelTheta_represents_latentDirac (hprefix := hprefix)
  exact
    deFinettiStable_markovCore_to_kleisliIsLimit_of_globalFinitaryInvariance_and_defaultAllSourcesKernel_and_latentDirac
      (Y := Y) (Ω := Ω) (X := X)
      hcore hglobal hrepDirac hunivDefault hmarkov_of_commutes

/-- Stable export: global cross-`n` categorical package from prefix-law
exchangeability. -/
def deFinettiStable_exchangeableCrossNLimitPackage_of_isPrefixLawCone
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (hcone : IsPrefixLawCone (Ω := Ω) X μ) :
    ExchangeableCrossNLimitPackage (Ω := Ω) X μ :=
  exchangeableCrossNLimitPackage_of_isPrefixLawCone (Ω := Ω) X μ hcone

/-- Stable export: substantive equivalence between the per-`n` uniqueness package
and the global cross-`n` package family. -/
theorem deFinettiStable_perNUnique_iff_crossNPackageFamily
    (X : ℕ → Ω → Bool) :
    ExchangeablePerNLimitMediatorUnique (Ω := Ω) X ↔
      ∀ μ : Measure Ω, IsPrefixLawCone (Ω := Ω) X μ →
        Nonempty (ExchangeableCrossNLimitPackage (Ω := Ω) X μ) :=
  exchangeablePerNLimitMediatorUnique_iff_crossNPackageFamily (Ω := Ω) X

/-- Stable export: uniqueness check between any two mediators satisfying the same
cross-`n` factorization equations. -/
theorem deFinettiStable_exchangeableCrossNLimitPackage_mediators_eq_of_fac
    (X : ℕ → Ω → Bool) (μ : Measure Ω)
    (pkg : ExchangeableCrossNLimitPackage (Ω := Ω) X μ)
    (n : ℕ) (m₁ m₂ : PUnit ⟶ PerNPrefixFixedPoints n)
    (hm₁ :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m₁ ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j)
    (hm₂ :
      ∀ j : PerNPermIndex n,
        CategoryTheory.CategoryStruct.comp m₂ ((perNPrefixFixedPointsCone n).π.app j) =
          (exchangeablePerNSourceCone (Ω := Ω) X μ n pkg.hcone).π.app j) :
    m₁ = m₂ :=
  exchangeableCrossNLimitPackage_mediators_eq_of_fac
    (Ω := Ω) X μ pkg n m₁ m₂ hm₁ hm₂

end Mettapedia.CategoryTheory
