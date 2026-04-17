import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CanonicalBridge

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v} {Const' : Ty Base → Type w}

namespace CompletenessFrontier

/-- Map a closed completeness frontier along a constant embedding into a larger
signature. This isolates the extended-signature route from the original one at
the level of frontier data rather than mixing both routes in the same theorem
statements. -/
def mapConstants
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (F : CompletenessFrontier Const []) :
    CompletenessFrontier Const' [] where
  antecedents := F.antecedents.map (Mettapedia.Logic.HOL.mapClosedFormula f)
  succedent := Mettapedia.Logic.HOL.mapClosedFormula f F.succedent

@[simp] theorem antecedents_mapConstants
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (F : CompletenessFrontier Const []) :
    (F.mapConstants f).antecedents =
      F.antecedents.map (Mettapedia.Logic.HOL.mapClosedFormula f) :=
  rfl

@[simp] theorem succedent_mapConstants
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (F : CompletenessFrontier Const []) :
    (F.mapConstants f).succedent =
      Mettapedia.Logic.HOL.mapClosedFormula f F.succedent :=
  rfl

/-- Native derivability in the original signature transports to extensional
set-provability on the mapped frontier in any larger signature. This is the
honest pullback direction available before a separate reflection theorem has
been proved. -/
theorem closedTheorySet_provable_mapConstants
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {F : CompletenessFrontier Const []} :
    Derivable (Base := Base) (Const := Const) F.antecedents F.succedent ->
      ClosedTheorySet.Provable (Const := Const')
        (F.mapConstants f).antecedentTheorySet (F.mapConstants f).succedent := by
  intro h
  refine ClosedTheorySet.provable_of_closedTheory
    (Const := Const')
    (T := (F.mapConstants f).antecedentTheorySet)
    (Δ := (F.mapConstants f).antecedents)
    (hΔ := by
      intro ψ hψ
      exact hψ) ?_
  simpa [CompletenessFrontier.mapConstants] using
    (Mettapedia.Logic.HOL.ExtDerivation.closedTheory_mapConst
      (Base := Base) (Const := Const) (Const' := Const') f
      h.toClosedTheoryProvable)

/-- Any extensional refutation of the mapped frontier in an extended signature
already refutes native derivability of the original frontier. This is the core
architectural pullback needed for an HInf-first route. -/
theorem not_derivable_of_mapped_not_closedTheorySetProvable
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {F : CompletenessFrontier Const []}
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const')
          (F.mapConstants f).antecedentTheorySet (F.mapConstants f).succedent) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  intro hDer
  exact hNot (F.closedTheorySet_provable_mapConstants (Const' := Const') f hDer)

/-- A world counterexample for the mapped frontier in an extended signature
already refutes derivability of the original frontier. -/
theorem not_derivable_of_mapped_world_counterexample
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {F : CompletenessFrontier Const []}
    {W : ClosedTheorySet.World Const'}
    (hAnte :
      ∀ phi, phi ∈ (F.mapConstants f).antecedents -> phi ∈ W.carrier)
    (hSucc : (F.mapConstants f).succedent ∉ W.carrier) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact F.not_derivable_of_mapped_not_closedTheorySetProvable
    (Const' := Const') f <|
      CompletenessFrontier.not_closedTheorySetProvable_of_world_counterexample
        (Base := Base) (Const := Const')
        (F := F.mapConstants f) (W := W) hAnte hSucc

/-- A mapped prime-separating extension already refutes native derivability of
the original frontier. The remaining work for an extended-signature
completeness route is therefore to produce such an extension honestly in the
larger signature, not to consume it once available. -/
theorem not_derivable_of_mapped_primeSeparatingExtension
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const'}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const') (F.mapConstants f) U) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact F.not_derivable_of_mapped_not_closedTheorySetProvable
    (Const' := Const') f hFU.not_setProvable_succedent

end CompletenessFrontier

namespace LocalHintikkaCertificate

/-- Any larger-signature world agreeing with a closed local Hintikka
certificate on every staged true/false formula already refutes derivability of
the original frontier. This factors the pullback consumer through the
paper-facing certificate layer instead of requiring each bridge to reconstruct
antecedent/succedent membership manually. -/
theorem not_derivable_of_mapped_worldAgreement
    {F : CompletenessFrontier Const []}
    (C : LocalHintikkaCertificate F)
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    {W : ClosedTheorySet.World Const'}
    (hTrue :
      ∀ {φ : ClosedFormula Const},
        (Sign.trueE, φ) ∈ C.hintikka.formulas →
          Mettapedia.Logic.HOL.mapClosedFormula f φ ∈ W.carrier)
    (hFalse :
      ∀ {φ : ClosedFormula Const},
        (Sign.falseE, φ) ∈ C.hintikka.formulas →
          Mettapedia.Logic.HOL.mapClosedFormula f φ ∉ W.carrier) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact CompletenessFrontier.not_derivable_of_mapped_world_counterexample
    (Base := Base) (Const := Const) (Const' := Const') (f := f) (F := F) (W := W)
    (fun ψ hψ => by
      rcases List.mem_map.mp hψ with ⟨φ, hφ, rfl⟩
      exact hTrue (C.antecedent_true_mem hφ))
    (by
      simpa [CompletenessFrontier.mapConstants] using hFalse C.succedent_false_mem)

end LocalHintikkaCertificate

namespace CertifiedCountermodelCandidate

/-- A mapped world that agrees with the certified closed Hintikka hull can be
consumed directly at the certified-candidate layer via the generic
certificate-facing pullback theorem. -/
theorem not_derivable_of_exists_mapped_worldAgreement
    (C : CertifiedCountermodelCandidate Const [])
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (hW :
      ∃ W : ClosedTheorySet.World Const',
        (∀ {φ : ClosedFormula Const},
          (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
            Mettapedia.Logic.HOL.mapClosedFormula f φ ∈ W.carrier) ∧
        (∀ {φ : ClosedFormula Const},
          (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
            Mettapedia.Logic.HOL.mapClosedFormula f φ ∉ W.carrier)) :
    ¬ Derivable (Base := Base) (Const := Const)
      C.frontier.antecedents C.frontier.succedent := by
  rcases hW with ⟨W, hTrue, hFalse⟩
  exact C.toClosedLocalHintikkaCertificate.not_derivable_of_mapped_worldAgreement
    (Const' := Const') (f := f) (W := W) hTrue hFalse

end CertifiedCountermodelCandidate

namespace CertifiedHeadPriorityCompletion

/-- A mapped world that agrees with the certified completion's closed
Hintikka hull can be consumed directly at the certified-completion layer via
the generic certificate-facing pullback theorem. -/
theorem not_derivable_of_exists_mapped_worldAgreement
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (f : ∀ {τ : Ty Base}, Const τ → Const' τ)
    (hW :
      ∃ W : ClosedTheorySet.World Const',
        (∀ {φ : ClosedFormula Const},
          (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
            Mettapedia.Logic.HOL.mapClosedFormula f φ ∈ W.carrier) ∧
        (∀ {φ : ClosedFormula Const},
          (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
            Mettapedia.Logic.HOL.mapClosedFormula f φ ∉ W.carrier)) :
    ¬ Derivable (Base := Base) (Const := Const)
      F.antecedents F.succedent := by
  rcases hW with ⟨W, hTrue, hFalse⟩
  exact C.toClosedLocalHintikkaCertificate.not_derivable_of_mapped_worldAgreement
    (Const' := Const') (f := f) (W := W) hTrue hFalse

end CertifiedHeadPriorityCompletion

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
