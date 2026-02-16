import Mettapedia.CategoryTheory.DeFinettiKernelInterface
import Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection

/-!
# Sequence-Kernel Permutation Cone and IID Prefix Kernels

This file adds:
1. A sequence-level permutation-cone interface on kernels `κ : Y → (ℕ → Bool)`.
2. An explicit iid prefix-kernel family (in Mathlib's `Kernel` layer) and direct
   permutation commutation on singleton cylinder events.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open MeasureTheory
open ProbabilityTheory
open Mettapedia.Logic.Exchangeability
open Mettapedia.Logic.DeFinetti

variable {Y : Type*} [MeasurableSpace Y]

/-- Canonical binary sequence space `Bool^ℕ`. -/
abbrev BinarySeq : Type := ℕ → Bool

/-- Prefix cylinder event on `Bool^ℕ`. -/
def seqPrefixEvent (n : ℕ) (xs : Fin n → Bool) : Set BinarySeq :=
  {ω | ∀ i : Fin n, ω i = xs i}

/-- Finite-prefix tuple permutation action. -/
def permutePrefixTuple {n : ℕ} (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool) : Fin n → Bool :=
  xs ∘ σ.symm

/-- Sequence-kernel permutation cone:
for each parameter `y`, finite-prefix laws commute with finite-coordinate
permutations. -/
def KernelSequencePrefixCone
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop :=
  ∀ (y : Y) (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
    (κ y) (seqPrefixEvent n xs) = (κ y) (seqPrefixEvent n (permutePrefixTuple σ xs))

/-- Thin cone-object wrapper for sequence-kernel permutation commutation. -/
structure SequenceKernelConeObj
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] : Prop where
  commutes :
    ∀ (y : Y) (n : ℕ) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
      (κ y) (seqPrefixEvent n xs) = (κ y) (seqPrefixEvent n (permutePrefixTuple σ xs))

/-- The thin cone-object wrapper is definitionally equivalent to
`KernelSequencePrefixCone`. -/
theorem sequenceKernelConeObj_iff_kernelSequencePrefixCone
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔ KernelSequencePrefixCone κ := by
  constructor
  · intro h
    exact h.commutes
  · intro h
    exact ⟨h⟩

/-- Coordinate process on sequence space. -/
def coordProcess : ℕ → BinarySeq → Bool :=
  fun i ω => ω i

/-- The new sequence-kernel cone is exactly the old kernel prefix-cone
for the coordinate process `coordProcess`. -/
theorem kernelSequencePrefixCone_iff_kernelPrefixCone_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    KernelSequencePrefixCone κ ↔ KernelPrefixCone (X := coordProcess) κ := by
  constructor
  · intro h y n σ xs
    simpa [KernelSequencePrefixCone, KernelPrefixCone, ExchangeablePrefixCone,
      prefixLaw, seqPrefixEvent, permutePrefixTuple, coordProcess, permuteBoolTuple] using
      h y n σ xs
  · intro h y n σ xs
    simpa [KernelSequencePrefixCone, KernelPrefixCone, ExchangeablePrefixCone,
      prefixLaw, seqPrefixEvent, permutePrefixTuple, coordProcess, permuteBoolTuple] using
      h y n σ xs

/-- Sequence-kernel cone is equivalent to pointwise exchangeability for the
coordinate process. -/
theorem kernelSequencePrefixCone_iff_kernelExchangeable_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    KernelSequencePrefixCone κ ↔ KernelExchangeable (X := coordProcess) κ := by
  rw [kernelSequencePrefixCone_iff_kernelPrefixCone_coord]
  simpa using
    (kernelExchangeable_iff_kernelPrefixCone (X := coordProcess) (κ := κ)).symm

/-- Cone-object API equivalence to coordinate-process exchangeability. -/
theorem sequenceKernelConeObj_iff_kernelExchangeable_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔ KernelExchangeable (X := coordProcess) κ := by
  rw [sequenceKernelConeObj_iff_kernelSequencePrefixCone]
  exact kernelSequencePrefixCone_iff_kernelExchangeable_coord (κ := κ)

/-- Bridge theorem from cone-object form to latent-`Theta` factorization:
a sequence-kernel cone object yields a unique latent `Y → Measure Theta` family
for the coordinate process. -/
theorem sequenceKernelConeObj_existsUnique_latentThetaKernel
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ →
      ∃! L :
        Y →
          Measure
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
        KernelRepresentsLatentTheta (X := coordProcess) κ L := by
  intro hcone
  have hexch : KernelExchangeable (X := coordProcess) κ :=
    (sequenceKernelConeObj_iff_kernelExchangeable_coord (κ := κ)).1 hcone
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    simpa [coordProcess] using (measurable_pi_apply (a := i))
  exact existsUnique_latentThetaKernel_of_kernelExchangeable
    (X := coordProcess) (κ := κ) hX hexch

/-- Round-trip bridge:
`SequenceKernelConeObj` is equivalent to latent-`Theta` factorization for the coordinate process,
and together with `sequenceKernelConeObj_existsUnique_latentThetaKernel` yields
existence-uniqueness of the mediator map. -/
theorem sequenceKernelConeObj_iff_kernelLatentThetaFactorization_coord
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔ KernelLatentThetaFactorization (X := coordProcess) κ := by
  have hX : ∀ i : ℕ, Measurable (coordProcess i) := by
    intro i
    simpa [coordProcess] using (measurable_pi_apply (a := i))
  calc
    SequenceKernelConeObj κ ↔ KernelExchangeable (X := coordProcess) κ :=
      sequenceKernelConeObj_iff_kernelExchangeable_coord (κ := κ)
    _ ↔ KernelLatentThetaFactorization (X := coordProcess) κ :=
      kernelExchangeable_iff_kernelLatentThetaFactorization (X := coordProcess) (κ := κ) hX

/-- Round-trip package combining cone-object/factorization equivalence with
the cone-object existence-uniqueness theorem for latent-`Theta` mediators. -/
theorem sequenceKernelConeObj_roundTrip_latentThetaMediator
    (κ : ProbabilityTheory.Kernel Y BinarySeq)
    [ProbabilityTheory.IsMarkovKernel κ] :
    SequenceKernelConeObj κ ↔
      (KernelLatentThetaFactorization (X := coordProcess) κ ∧
        ∃! L :
          Y →
            Measure
              Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta,
          KernelRepresentsLatentTheta (X := coordProcess) κ L) := by
  constructor
  · intro hcone
    refine ⟨(sequenceKernelConeObj_iff_kernelLatentThetaFactorization_coord (κ := κ)).1 hcone, ?_⟩
    exact sequenceKernelConeObj_existsUnique_latentThetaKernel (κ := κ) hcone
  · intro h
    exact (sequenceKernelConeObj_iff_kernelLatentThetaFactorization_coord (κ := κ)).2 h.1

/-! ## IID Prefix Kernels in Mathlib's Kernel Layer -/

/-- Parameter space `[0,1]` used by the Bernoulli mixture construction. -/
abbrev Theta : Type :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.Theta

/-- IID Bernoulli prefix-kernel (horizon `n`) from the higher-order probability
de Finetti connection file. -/
noncomputable abbrev iidPrefixKernel (n : ℕ) : ProbabilityTheory.Kernel Theta (Fin n → Bool) :=
  Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel (n := n)

instance iidPrefixKernel_isMarkov (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (iidPrefixKernel n) := by
  simpa [iidPrefixKernel] using
    (Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel_isMarkov
      (n := n))

/-- Direct permutation commutation on singleton prefix events for the iid prefix-kernel. -/
theorem iidPrefixKernel_perm_singleton
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (θ : Theta) (xs : Fin n → Bool) :
    (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) =
      (iidPrefixKernel n θ) ({xs ∘ σ.symm} : Set (Fin n → Bool)) := by
  have hcountTrue : countTrue (xs ∘ σ.symm) = countTrue xs := countTrue_perm xs σ.symm
  have hcountFalse : countFalse (xs ∘ σ.symm) = countFalse xs := countFalse_perm xs σ.symm
  have hprod :
      bernoulliProductPMF (θ : ℝ) xs =
        bernoulliProductPMF (θ : ℝ) (xs ∘ σ.symm) := by
    simp [bernoulliProductPMF_eq_power, hcountTrue, hcountFalse]
  have hweight :
      Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
          (n := n) θ xs =
        Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
          (n := n) θ (xs ∘ σ.symm) := by
    simp [Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight, hprod]
  calc
    (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool))
        =
          Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
            (n := n) θ xs := by
              simp [iidPrefixKernel,
                Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel]
    _ =
        Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.weight
          (n := n) θ (xs ∘ σ.symm) := hweight
    _ =
        (iidPrefixKernel n θ) ({xs ∘ σ.symm} : Set (Fin n → Bool)) := by
          simp [iidPrefixKernel,
            Mettapedia.ProbabilityTheory.HigherOrderProbability.DeFinettiConnection.kernel]

/-- Cone law for the iid prefix-kernel family:
finite-coordinate permutations preserve singleton prefix-event probabilities. -/
theorem iidPrefixKernel_cone_commutes
    (n : ℕ) :
    ∀ (θ : Theta) (σ : Equiv.Perm (Fin n)) (xs : Fin n → Bool),
      (iidPrefixKernel n θ) ({xs} : Set (Fin n → Bool)) =
        (iidPrefixKernel n θ) ({xs ∘ σ.symm} : Set (Fin n → Bool)) := by
  intro θ σ xs
  exact iidPrefixKernel_perm_singleton n σ θ xs

end Mettapedia.CategoryTheory
