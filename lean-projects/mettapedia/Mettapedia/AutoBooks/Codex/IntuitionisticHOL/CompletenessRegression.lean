import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

/-!
# Completeness Regression

Canaries around the current search-to-countermodel spine. In particular, these
examples record that arbitrary terminal head-priority completion does not by
itself force non-contradiction: a bad branch choice can still end in a
contradictory local candidate.
-/

namespace CompletenessRegression

open Mettapedia.Logic.HOL

inductive BaseSort where
  | atom
  deriving DecidableEq, Repr

def Const : Ty BaseSort → Type := fun _ => PEmpty

def badFrontier : CompletenessFrontier Const [] :=
  { antecedents := [.top]
    succedent := .and .top .top }

def badResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .falseAnd .top .top
    step := .falseAndLeft .top .top
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

@[simp] theorem badInitialAgenda :
    (SaturationSearchState.initial badFrontier).agenda =
      [LocalBranchTarget.falseAnd (.top : Formula Const []) (.top : Formula Const [])] := by
  simp [SaturationSearchState.initial, badFrontier, HintikkaSet.localBranchTargets,
    LocalBranchTarget.ofSignedFormula]

theorem badCanResolveHead :
    (SaturationSearchState.initial badFrontier).CanResolveHead badResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    badResolution]

def badState : SaturationSearchState Const [] :=
  { frontier := badFrontier
    hintikka :=
      { formulas :=
          [(Sign.falseE, (.top : Formula Const [])),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.falseE, (.and (.top : Formula Const []) (.top : Formula Const [])))] }
    agenda := [] }

@[simp] theorem badState_formulas :
    badState.hintikka.formulas =
      [(Sign.falseE, (.top : Formula Const [])),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.falseE, (.and (.top : Formula Const []) (.top : Formula Const [])))] := by
  rfl

@[simp] theorem badState_agenda : badState.agenda = [] := by
  rfl

theorem mem_badState_formulas {sf : SignedFormula Const []} :
    sf ∈ badState.hintikka.formulas ↔
      sf = (Sign.falseE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.falseE, (.and (.top : Formula Const []) (.top : Formula Const []))) := by
  simp [badState_formulas]

theorem badState_eq_resolveHead :
    badState =
      (SaturationSearchState.initial badFrontier).resolveHead
        badResolution badCanResolveHead := by
  rfl

theorem badState_noProductiveTriggeredStep :
    badState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseOr φ ψ =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_badState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h

theorem badState_branchClosed :
    badState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_badState_formulas.mp hprem
      rcases hprem' with h | h | h
      · cases h
      · cases h
      · cases h
        exact (mem_badState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
  | trueOr φ ψ =>
      refine ⟨.trueOrLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_badState_formulas.mp hprem
      rcases hprem' with h | h | h <;> cases h

theorem badState_terminal : badState.IsTerminal := by
  exact ⟨badState_agenda, badState_noProductiveTriggeredStep⟩

def badDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation badFrontier badState :=
  by
    simpa [badState_eq_resolveHead] using
      (SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
        (F := badFrontier)
        SaturationSearchState.HeadPrioritySearchDerivation.initial
        badResolution badCanResolveHead)

def badCompletion : SaturationSearchState.HeadPriorityCompletion badFrontier :=
  { state := badState
    derivation := badDerivation
    terminal := badState_terminal
    branchClosed := badState_branchClosed }

def badCandidate : CountermodelCandidate Const [] :=
  { frontier := badFrontier
    completion := badCompletion }

theorem badFrontier_derivable :
    Derivable (Base := BaseSort) (Const := Const)
      badFrontier.antecedents badFrontier.succedent := by
  refine Derivable.andR ?_ ?_
  · exact Derivable.ax (by simp [badFrontier])
  · exact Derivable.ax (by simp [badFrontier])

theorem badInitialHintikka_not_icttConsistent :
    ¬ badFrontier.initialHintikkaSet.ICTTConsistent := by
  rw [CompletenessFrontier.initialHintikkaSet_icttConsistent_iff_not_derivable]
  intro hNot
  exact hNot badFrontier_derivable

theorem badCandidate_closedHintikka_not_icttConsistent :
    ¬ badCandidate.closedHintikka.ICTTConsistent := by
  intro hCons
  have hFalseTop :
      (Sign.falseE, (.top : Formula Const [])) ∈ badCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by simp [badCandidate, CountermodelCandidate.hintikka,
      CountermodelCandidate.state, badCompletion])
  exact (HintikkaSet.not_derivable_of_false_mem_of_icttConsistent hCons hFalseTop)
    Derivable.topR

theorem badCandidate_closedHintikka_not_noncontradictory :
    ¬ badCandidate.closedHintikka.Noncontradictory := by
  intro h
  have hTrue :
      (Sign.trueE, (.top : Formula Const [])) ∈ badCandidate.closedHintikka.formulas := by
    exact badCandidate.true_mem_closedHintikka (by simp [badCandidate, badFrontier])
  have hFalse :
      (Sign.falseE, (.top : Formula Const [])) ∈ badCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by simp [badCandidate, CountermodelCandidate.hintikka,
      CountermodelCandidate.state, badCompletion])
  exact h (HintikkaSet.contradictory_of_conflict hTrue hFalse)

theorem not_all_terminal_candidates_noncontradictory :
    ¬ ∀ C : CountermodelCandidate Const [], C.closedHintikka.Noncontradictory := by
  intro h
  exact badCandidate_closedHintikka_not_noncontradictory (h badCandidate)

theorem not_all_terminal_candidates_icttConsistent :
    ¬ ∀ C : CountermodelCandidate Const [], C.closedHintikka.ICTTConsistent := by
  intro h
  exact badCandidate_closedHintikka_not_icttConsistent (h badCandidate)

example :
    badState.IsTerminal :=
  badState_terminal

example :
    ¬ badCandidate.closedHintikka.Noncontradictory :=
  badCandidate_closedHintikka_not_noncontradictory

example :
    ¬ badCandidate.closedHintikka.ICTTConsistent :=
  badCandidate_closedHintikka_not_icttConsistent

/-- Trivial global model used to separate an underivable frontier from a bad
branch choice. -/
def underivableCarrier : Ty BaseSort → Type
  | .prop => Prop
  | .base _ => PUnit
  | .arr σ τ => underivableCarrier σ → underivableCarrier τ

def underivableModel : GlobalModel BaseSort Const where
  toSemilocalModel :=
    { toApplicativeStructure :=
        { Carrier := underivableCarrier
          const := fun c => nomatch c
          app := fun f x => f x
          lam := fun f => f
          beta := by
            intro σ τ f x
            rfl
          eta := by
            intro σ τ f
            rfl }
      Omega := Prop
      frame := inferInstance
      truth := fun p => p
      extent := fun _ => True
      topP := True
      botP := False
      andP := And
      orP := Or
      impP := fun p q => p → q
      eqP := fun x y => x = y
      allP := fun f => ∀ x, f x
      exP := fun f => ∃ x, f x
      truth_top := rfl
      truth_bot := rfl
      truth_and := by
        intro p q
        rfl
      truth_or := by
        intro p q
        rfl
      truth_imp := by
        intro p q
        rfl
      truth_all := by
        intro σ f
        apply propext
        simp
      truth_ex := by
        intro σ f
        apply propext
        simp }
  global := by
    intro τ x
    rfl

def underivableEmptyEnv : GlobalModel.Env underivableModel [] :=
  fun {_τ} v => nomatch v

def underivableSemilocalGlobal :
    SemilocalModel.IsGlobalEnv underivableModel.toSemilocalModel underivableEmptyEnv :=
  GlobalModel.isGlobalEnv underivableModel underivableEmptyEnv

def underivableSemilocalSupportsUniformRelativization :
    SemilocalModel.SupportsUniformRelativization underivableModel.toSemilocalModel :=
  GlobalModel.supportsUniformRelativization underivableModel

def underivableFrontier : CompletenessFrontier Const [] :=
  { antecedents := [.top, .or .bot .top]
    succedent := .bot }

theorem underivableFrontier_not_valid :
    ¬ GlobalModel.ValidSequent underivableModel
      underivableFrontier.antecedents underivableFrontier.succedent := by
  intro hvalid
  have h := hvalid underivableEmptyEnv
  simp [GlobalModel.antecedentTruth, GlobalModel.formulaTruth, SemilocalModel.antecedentTruth,
    SemilocalModel.formulaTruth, SemilocalModel.eval, underivableFrontier,
    underivableModel] at h

theorem underivableFrontier_not_derivable :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      underivableFrontier.antecedents underivableFrontier.succedent := by
  intro hDer
  exact underivableFrontier_not_valid (GlobalModel.soundness underivableModel hDer)

theorem underivableInitialHintikka_icttConsistent :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent := by
  rw [CompletenessFrontier.initial_icttConsistent_iff_not_derivable]
  exact underivableFrontier_not_derivable

theorem underivableFrontier_closedNonconflicting :
    underivableFrontier.ClosedNonconflicting := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [underivableFrontier]

def underivableResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .trueOr .bot .top
    step := .trueOrLeft .bot .top
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

@[simp] theorem underivableInitialAgenda :
    (SaturationSearchState.initial underivableFrontier).agenda =
      [LocalBranchTarget.trueOr (.bot : Formula Const []) (.top : Formula Const [])] := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.localBranchTargets,
    LocalBranchTarget.ofSignedFormula]

theorem underivableCanResolveHead :
    (SaturationSearchState.initial underivableFrontier).CanResolveHead underivableResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    underivableResolution]

def goodResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .trueOr .bot .top
    step := .trueOrRight .bot .top
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

theorem goodCanResolveHead :
    (SaturationSearchState.initial underivableFrontier).CanResolveHead goodResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    goodResolution]

def goodState : SaturationSearchState Const [] :=
  { frontier := underivableFrontier
    hintikka :=
      { formulas :=
          [(Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
            (Sign.falseE, (.bot : Formula Const []))] }
    agenda := [] }

@[simp] theorem goodState_formulas :
    goodState.hintikka.formulas =
      [(Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
        (Sign.falseE, (.bot : Formula Const []))] := by
  rfl

theorem mem_goodState_formulas {sf : SignedFormula Const []} :
    sf ∈ goodState.hintikka.formulas ↔
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))) ∨
      sf = (Sign.falseE, (.bot : Formula Const [])) := by
  simp [goodState_formulas]

@[simp] theorem goodState_agenda : goodState.agenda = [] := by
  rfl

theorem goodState_eq_resolveHead :
    goodState =
      (SaturationSearchState.initial underivableFrontier).resolveHead
        goodResolution goodCanResolveHead := by
  rfl

theorem goodState_noProductiveTriggeredStep :
    goodState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseOr φ ψ =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_goodState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h

theorem goodState_branchClosed :
    goodState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_goodState_formulas.mp hprem
      rcases hprem' with h | h | h | h <;> cases h
  | trueOr φ ψ =>
      refine ⟨.trueOrRight φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_goodState_formulas.mp hprem
      rcases hprem' with h | h | h | h
      · cases h
      · cases h
      · cases h
        exact (mem_goodState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
      · cases h

theorem goodState_terminal : goodState.IsTerminal := by
  exact ⟨goodState_agenda, goodState_noProductiveTriggeredStep⟩

def goodDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation underivableFrontier goodState :=
  by
    simpa [goodState_eq_resolveHead] using
      (SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
        (F := underivableFrontier)
        SaturationSearchState.HeadPrioritySearchDerivation.initial
        goodResolution goodCanResolveHead)

def goodCompletion : SaturationSearchState.HeadPriorityCompletion underivableFrontier :=
  { state := goodState
    derivation := goodDerivation
    terminal := goodState_terminal
    branchClosed := goodState_branchClosed }

def goodCandidate : CountermodelCandidate Const [] :=
  { frontier := underivableFrontier
    completion := goodCompletion }

def underivableState : SaturationSearchState Const [] :=
  { frontier := underivableFrontier
    hintikka :=
      { formulas :=
          [(Sign.trueE, (.bot : Formula Const [])),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
            (Sign.falseE, (.bot : Formula Const []))] }
    agenda := [] }

@[simp] theorem underivableState_formulas :
    underivableState.hintikka.formulas =
      [(Sign.trueE, (.bot : Formula Const [])),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))),
        (Sign.falseE, (.bot : Formula Const []))] := by
  rfl

theorem mem_underivableState_formulas {sf : SignedFormula Const []} :
    sf ∈ underivableState.hintikka.formulas ↔
      sf = (Sign.trueE, (.bot : Formula Const [])) ∨
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.or (.bot : Formula Const []) (.top : Formula Const []))) ∨
      sf = (Sign.falseE, (.bot : Formula Const [])) := by
  simp [underivableState_formulas]

@[simp] theorem underivableState_agenda : underivableState.agenda = [] := by
  rfl

theorem underivableState_eq_resolveHead :
    underivableState =
      (SaturationSearchState.initial underivableFrontier).resolveHead
        underivableResolution underivableCanResolveHead := by
  rfl

theorem underivableState_noProductiveTriggeredStep :
    underivableState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseOr φ ψ =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_underivableState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h

theorem underivableState_branchClosed :
    underivableState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_underivableState_formulas.mp hprem
      rcases hprem' with h | h | h | h <;> cases h
  | trueOr φ ψ =>
      refine ⟨.trueOrLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_underivableState_formulas.mp hprem
      rcases hprem' with h | h | h | h
      · cases h
      · cases h
      · cases h
        exact (mem_underivableState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
      · cases h

theorem underivableState_terminal : underivableState.IsTerminal := by
  exact ⟨underivableState_agenda, underivableState_noProductiveTriggeredStep⟩

def underivableDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation underivableFrontier underivableState :=
  by
    simpa [underivableState_eq_resolveHead] using
      (SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
        (F := underivableFrontier)
        SaturationSearchState.HeadPrioritySearchDerivation.initial
        underivableResolution underivableCanResolveHead)

def underivableCompletion : SaturationSearchState.HeadPriorityCompletion underivableFrontier :=
  { state := underivableState
    derivation := underivableDerivation
    terminal := underivableState_terminal
    branchClosed := underivableState_branchClosed }

def underivableCandidate : CountermodelCandidate Const [] :=
  { frontier := underivableFrontier
    completion := underivableCompletion }

theorem underivableCandidate_closedHintikka_not_noncontradictory :
    ¬ underivableCandidate.closedHintikka.Noncontradictory := by
  intro h
  have hTrueBot :
      (Sign.trueE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  have hFalseBot :
      (Sign.falseE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  exact h (HintikkaSet.contradictory_of_conflict hTrueBot hFalseBot)

theorem underivableCandidate_closedHintikka_not_icttConsistent :
    ¬ underivableCandidate.closedHintikka.ICTTConsistent := by
  intro hCons
  have hTrueBot :
      (Sign.trueE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  have hFalseBot :
      (Sign.falseE, (.bot : Formula Const [])) ∈ underivableCandidate.closedHintikka.formulas := by
    exact HintikkaSet.mem_close_of_mem (by
      simp [underivableCandidate, CountermodelCandidate.hintikka,
        CountermodelCandidate.state, underivableCompletion])
  exact (HintikkaSet.not_derivable_of_false_mem_of_icttConsistent hCons hFalseBot)
    (HintikkaSet.derivable_of_true_mem hTrueBot)

theorem underivableResolution_breaks_initial_icttConsistent :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent ∧
      ¬ ((SaturationSearchState.initial underivableFrontier).resolveHead
          underivableResolution underivableCanResolveHead).hintikka.close.ICTTConsistent := by
  constructor
  · exact underivableInitialHintikka_icttConsistent
  · simpa [underivableState_eq_resolveHead, CountermodelCandidate.closedHintikka,
      CountermodelCandidate.hintikka, CountermodelCandidate.state, underivableCandidate,
      underivableCompletion] using underivableCandidate_closedHintikka_not_icttConsistent

theorem underivableInitialClosedHintikka_false_mem_iff_bot {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas ↔
      φ = (.bot : Formula Const []) := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_true_mem_iff
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas ↔
      φ = (.top : Formula Const []) ∨
        φ = (.or (.bot : Formula Const []) (.top : Formula Const [])) := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_trueBot_not_mem :
    (Sign.trueE, (.bot : Formula Const [])) ∉
      (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_falseTop_not_mem :
    (Sign.falseE, (.top : Formula Const [])) ∉
      (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
  simp [SaturationSearchState.initial, underivableFrontier, HintikkaSet.close]

theorem underivableInitialClosedHintikka_noncontradictory :
    (SaturationSearchState.initial underivableFrontier).hintikka.close.Noncontradictory := by
  exact (CompletenessFrontier.initial_closed_noncontradictory_iff underivableFrontier).2
    underivableFrontier_closedNonconflicting

theorem goodResolution_branchAdditionCompatible :
    (SaturationSearchState.initial underivableFrontier).BranchAdditionCompatible goodResolution := by
  rw [SaturationSearchState.branchAdditionCompatible_trueOrRight_iff
    (S := SaturationSearchState.initial underivableFrontier)
    (r := goodResolution) (φ := .bot) (ψ := .top) rfl]
  simpa [SignedFormula.flip] using underivableInitialClosedHintikka_falseTop_not_mem

theorem goodDerivation_compatible :
    SaturationSearchState.HeadPrioritySearchDerivation.Compatible goodDerivation := by
  simpa [goodDerivation, goodState_eq_resolveHead,
    SaturationSearchState.HeadPrioritySearchDerivation.Compatible] using
    SaturationSearchState.HeadPrioritySearchDerivation.compatible_resolveHead
      (D := SaturationSearchState.HeadPrioritySearchDerivation.initial (F := underivableFrontier))
      (r := goodResolution)
      (hhead := goodCanResolveHead)
      (by
        exact SaturationSearchState.HeadPrioritySearchDerivation.compatible_initial)
      goodResolution_branchAdditionCompatible

def deterministicWitnessFormula : Formula Const [] :=
  .or (.top : Formula Const []) (.top : Formula Const [])

def deterministicTriggerFormula : Formula Const [] :=
  .and deterministicWitnessFormula (.top : Formula Const [])

def deterministicFrontier : CompletenessFrontier Const [] :=
  { antecedents := [deterministicTriggerFormula]
    succedent := deterministicWitnessFormula }

theorem deterministicFrontier_closedNonconflicting :
    deterministicFrontier.ClosedNonconflicting := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [deterministicFrontier, deterministicTriggerFormula, deterministicWitnessFormula]

@[simp] theorem deterministicInitialAgenda :
    (SaturationSearchState.initial deterministicFrontier).agenda = [] := by
  simp [SaturationSearchState.initial, deterministicFrontier, deterministicWitnessFormula,
    deterministicTriggerFormula, HintikkaSet.localBranchTargets, LocalBranchTarget.ofSignedFormula]

def deterministicProductiveStep :
    SaturationSearchState.ProductiveTriggeredLocalStep
      (SaturationSearchState.initial deterministicFrontier) :=
  { step := .trueAnd deterministicWitnessFormula (.top : Formula Const [])
    active := by
      simpa [deterministicFrontier, deterministicTriggerFormula]
        using SaturationSearchState.true_mem_initial
          (F := deterministicFrontier) (φ := deterministicTriggerFormula)
            (by exact List.mem_singleton_self _)
    fresh := by
      refine ⟨(Sign.trueE, deterministicWitnessFormula), ?_, ?_⟩
      · simp [DeterministicLocalSaturationStep.additions, DeterministicLocalSaturationStep.toLocalSaturationStep,
          LocalSaturationStep.additions, deterministicWitnessFormula]
      · intro hmem
        simp [SaturationSearchState.initial, deterministicFrontier, deterministicTriggerFormula,
          deterministicWitnessFormula] at hmem
        rcases hmem with hmem | hmem <;>
          cases hmem }

def deterministicState : SaturationSearchState Const [] :=
  SaturationSearchState.applyLocalStep
    (SaturationSearchState.initial deterministicFrontier)
    deterministicProductiveStep.step.toLocalSaturationStep

@[simp] theorem deterministicState_eq_applyLocalStep :
    deterministicState =
      SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial deterministicFrontier)
        deterministicProductiveStep.step.toLocalSaturationStep := by
  rfl

theorem deterministicInitialClosedHintikka_true_mem_iff
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ (SaturationSearchState.initial deterministicFrontier).hintikka.close.formulas ↔
      φ = (.top : Formula Const []) ∨ φ = deterministicTriggerFormula := by
  simp [SaturationSearchState.initial, deterministicFrontier, deterministicWitnessFormula,
    deterministicTriggerFormula, HintikkaSet.close]

theorem deterministicInitialClosedHintikka_false_mem_iff
    {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ (SaturationSearchState.initial deterministicFrontier).hintikka.close.formulas ↔
      φ = (.bot : Formula Const []) ∨ φ = deterministicWitnessFormula := by
  simp [SaturationSearchState.initial, deterministicFrontier, deterministicWitnessFormula,
    deterministicTriggerFormula, HintikkaSet.close]

theorem deterministicInitialClosedHintikka_noncontradictory :
    (SaturationSearchState.initial deterministicFrontier).hintikka.close.Noncontradictory := by
  exact (CompletenessFrontier.initial_closed_noncontradictory_iff deterministicFrontier).2
    deterministicFrontier_closedNonconflicting

theorem deterministicStep_not_compatible :
    ¬ (SaturationSearchState.initial deterministicFrontier).DeterministicAdditionCompatible
      deterministicProductiveStep.step := by
  rw [show deterministicProductiveStep.step =
      DeterministicLocalSaturationStep.trueAnd deterministicWitnessFormula (.top : Formula Const []) by
      rfl]
  rw [SaturationSearchState.deterministicAdditionCompatible_trueAnd_iff
    (S := SaturationSearchState.initial deterministicFrontier)]
  intro hCompat
  have hFalse :
      (Sign.falseE, deterministicWitnessFormula) ∈
        (SaturationSearchState.initial deterministicFrontier).hintikka.close.formulas := by
    exact HintikkaSet.mem_close_of_mem
      (SaturationSearchState.false_mem_initial deterministicFrontier)
  exact hCompat.1 hFalse

def trueAndFrontier : CompletenessFrontier Const [] :=
  { antecedents := [.and (.top : Formula Const []) (.top : Formula Const [])]
    succedent := .bot }

theorem trueAndFrontier_closedNonconflicting :
    trueAndFrontier.ClosedNonconflicting := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [trueAndFrontier]

@[simp] theorem trueAndInitialAgenda :
    (SaturationSearchState.initial trueAndFrontier).agenda = [] := by
  simp [SaturationSearchState.initial, trueAndFrontier, HintikkaSet.localBranchTargets,
    LocalBranchTarget.ofSignedFormula]

def trueAndProductiveStep :
    SaturationSearchState.ProductiveTriggeredLocalStep
      (SaturationSearchState.initial trueAndFrontier) :=
  { step := .trueAnd (.top : Formula Const []) (.top : Formula Const [])
    active := by
      simpa [trueAndFrontier]
        using SaturationSearchState.true_mem_initial
          (F := trueAndFrontier)
          (φ := .and (.top : Formula Const []) (.top : Formula Const []))
          (by exact List.mem_singleton_self _)
    fresh := by
      refine ⟨(Sign.trueE, (.top : Formula Const [])), ?_, ?_⟩
      · simp [DeterministicLocalSaturationStep.additions,
          DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions]
      · intro hmem
        simp [SaturationSearchState.initial, trueAndFrontier] at hmem
        rcases hmem with hmem | hmem <;> cases hmem }

def trueAndState : SaturationSearchState Const [] :=
  { frontier := trueAndFrontier
    hintikka :=
      { formulas :=
          [(Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, (.and (.top : Formula Const []) (.top : Formula Const []))),
            (Sign.falseE, (.bot : Formula Const []))] }
    agenda := [] }

@[simp] theorem trueAndState_formulas :
    trueAndState.hintikka.formulas =
      [(Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, (.and (.top : Formula Const []) (.top : Formula Const []))),
        (Sign.falseE, (.bot : Formula Const []))] := by
  rfl

theorem mem_trueAndState_formulas {sf : SignedFormula Const []} :
    sf ∈ trueAndState.hintikka.formulas ↔
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, (.and (.top : Formula Const []) (.top : Formula Const []))) ∨
      sf = (Sign.falseE, (.bot : Formula Const [])) := by
  simp [trueAndState_formulas]

@[simp] theorem trueAndState_agenda : trueAndState.agenda = [] := by
  rfl

theorem trueAndState_eq_applyLocalStep :
    trueAndState =
      SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial trueAndFrontier)
        trueAndProductiveStep.step.toLocalSaturationStep := by
  rfl

theorem trueAndState_noProductiveTriggeredStep :
    trueAndState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_trueAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h
      · cases h
      · cases h
        rcases hfresh with ⟨sf, hsf, hnot⟩
        have hmem : sf ∈ trueAndState.hintikka.formulas := by
          simp [DeterministicLocalSaturationStep.additions,
            DeterministicLocalSaturationStep.toLocalSaturationStep,
            LocalSaturationStep.additions, trueAndState_formulas] at hsf ⊢
          simp [hsf]
        exact hnot hmem
      · cases h
  | falseOr φ ψ =>
      have hs' := mem_trueAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_trueAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_trueAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_trueAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_trueAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h <;> cases h

theorem trueAndState_branchClosed :
    trueAndState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_trueAndState_formulas.mp hprem
      rcases hprem' with h | h | h <;> cases h
  | trueOr φ ψ =>
      refine ⟨.trueOrLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_trueAndState_formulas.mp hprem
      rcases hprem' with h | h | h <;> cases h

theorem trueAndState_terminal : trueAndState.IsTerminal := by
  exact ⟨trueAndState_agenda, trueAndState_noProductiveTriggeredStep⟩

def trueAndDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation trueAndFrontier trueAndState := by
  simpa [trueAndState_eq_applyLocalStep] using
    (SaturationSearchState.HeadPrioritySearchDerivation.saturate
      (F := trueAndFrontier)
      SaturationSearchState.HeadPrioritySearchDerivation.initial
      trueAndInitialAgenda
      trueAndProductiveStep)

theorem trueAndInitialClosedHintikka_falseTop_not_mem :
    (Sign.falseE, (.top : Formula Const [])) ∉
      (SaturationSearchState.initial trueAndFrontier).hintikka.close.formulas := by
  simp [SaturationSearchState.initial, trueAndFrontier, HintikkaSet.close]

theorem trueAndProductiveStep_compatible :
    (SaturationSearchState.initial trueAndFrontier).DeterministicAdditionCompatible
      trueAndProductiveStep.step := by
  rw [show trueAndProductiveStep.step =
      DeterministicLocalSaturationStep.trueAnd (.top : Formula Const []) (.top : Formula Const []) by
      rfl]
  exact SaturationSearchState.deterministicAdditionCompatible_trueAnd
    (S := SaturationSearchState.initial trueAndFrontier)
    trueAndInitialClosedHintikka_falseTop_not_mem
    trueAndInitialClosedHintikka_falseTop_not_mem

theorem trueAndDerivation_compatible :
    SaturationSearchState.HeadPrioritySearchDerivation.Compatible trueAndDerivation := by
  simpa [trueAndDerivation, trueAndState_eq_applyLocalStep,
    SaturationSearchState.HeadPrioritySearchDerivation.Compatible] using
    SaturationSearchState.HeadPrioritySearchDerivation.compatible_saturate
      (D := SaturationSearchState.HeadPrioritySearchDerivation.initial (F := trueAndFrontier))
      (hIdle := trueAndInitialAgenda)
      (t := trueAndProductiveStep)
      (by
        exact SaturationSearchState.HeadPrioritySearchDerivation.compatible_initial)
      trueAndProductiveStep_compatible

def trueAndCertifiedDerivation :
    CertifiedHeadPriorityDerivation Const [] trueAndFrontier :=
  CertifiedHeadPriorityDerivation.ofInitialSaturate
    (Const := Const) (Γ := [])
    trueAndFrontier_closedNonconflicting
    trueAndInitialAgenda
    trueAndProductiveStep
    trueAndProductiveStep_compatible

@[simp] theorem trueAndCertifiedDerivation_state :
    trueAndCertifiedDerivation.state = trueAndState := by
  simpa [trueAndCertifiedDerivation, CertifiedHeadPriorityDerivation.ofInitialSaturate,
    CertifiedHeadPriorityDerivation.saturate, CertifiedHeadPriorityDerivation.initial] using
    trueAndState_eq_applyLocalStep

theorem trueAndCertifiedDerivation_terminal :
    trueAndCertifiedDerivation.state.IsTerminal := by
  simpa using trueAndState_terminal

theorem trueAndCertifiedDerivation_branchClosed :
    trueAndCertifiedDerivation.state.hintikka.BranchClosed := by
  simpa using trueAndState_branchClosed

theorem trueAndCertifiedDerivation_closedHintikka_noncontradictory :
    trueAndCertifiedDerivation.state.hintikka.close.Noncontradictory := by
  exact trueAndCertifiedDerivation.closedHintikka_noncontradictory

def trueAndCompletion : SaturationSearchState.HeadPriorityCompletion trueAndFrontier :=
  { state := trueAndState
    derivation := trueAndDerivation
    terminal := trueAndState_terminal
    branchClosed := trueAndState_branchClosed }

def trueAndCandidate : CountermodelCandidate Const [] :=
  { frontier := trueAndFrontier
    completion := trueAndCompletion }

def trueAndCertifiedCompletion :
    CertifiedHeadPriorityCompletion Const [] trueAndFrontier :=
  trueAndCertifiedDerivation.toCertifiedCompletion
    trueAndCertifiedDerivation_terminal
    trueAndCertifiedDerivation_branchClosed

def trueAndCertifiedCandidate : CertifiedCountermodelCandidate Const [] :=
  trueAndCertifiedDerivation.toCertifiedCountermodelCandidate
    trueAndCertifiedDerivation_terminal
    trueAndCertifiedDerivation_branchClosed

theorem trueAndCandidate_closedHintikka_noncontradictory :
    trueAndCandidate.closedHintikka.Noncontradictory := by
  exact trueAndCertifiedCandidate.closedHintikka_noncontradictory

def trueAndClosedCertificate : LocalHintikkaCertificate trueAndFrontier :=
  trueAndCertifiedDerivation.toClosedLocalHintikkaCertificate
    trueAndCertifiedDerivation_terminal
    trueAndCertifiedDerivation_branchClosed

theorem trueAndCandidate_closedHintikka_true_mem_iff
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ trueAndCandidate.closedHintikka.formulas ↔
      φ = (.top : Formula Const []) ∨
        φ = (.and (.top : Formula Const []) (.top : Formula Const [])) := by
  simp [trueAndCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, trueAndCompletion, trueAndState_formulas, HintikkaSet.close]

theorem trueAndCandidate_closedHintikka_false_mem_iff_bot
    {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ trueAndCandidate.closedHintikka.formulas ↔
      φ = (.bot : Formula Const []) := by
  simp [trueAndCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, trueAndCompletion, trueAndState_formulas, HintikkaSet.close]

def trueAndClosedHintikkaSemantics :
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      trueAndCertifiedDerivation
      trueAndCertifiedDerivation_terminal
      trueAndCertifiedDerivation_branchClosed
      underivableEmptyEnv :=
  { trueClass := fun ψ =>
      ψ = (.top : Formula Const []) ∨
        ψ = (.and (.top : Formula Const []) (.top : Formula Const []))
    falseClass := fun ψ => ψ = (.bot : Formula Const [])
    candidate_true_class := by
      intro φ hφ
      exact trueAndCandidate_closedHintikka_true_mem_iff.mp hφ
    candidate_false_class := by
      intro φ hφ
      exact trueAndCandidate_closedHintikka_false_mem_iff_bot.mp hφ
    true_top_of_class := by
      intro φ hφ
      rcases hφ with rfl | rfl <;> simp
    false_ne_top_of_class := by
      intro φ hφ
      subst hφ
      intro h
      simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h }

theorem trueAndCertifiedDerivation_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ trueAndCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  exact trueAndClosedHintikkaSemantics.closedHintikka_true_top hφ

theorem trueAndCertifiedDerivation_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ trueAndCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  exact trueAndClosedHintikkaSemantics.closedHintikka_false_ne_top hφ

theorem trueAndClosed_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ trueAndCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  rcases trueAndCandidate_closedHintikka_true_mem_iff.mp hφ with rfl | rfl
  · simp
  · simp

theorem trueAndClosed_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ trueAndCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  have hBot : φ = (.bot : Formula Const []) :=
    trueAndCandidate_closedHintikka_false_mem_iff_bot.mp hφ
  subst hBot
  intro h
  simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h

def trueAndClosedAgreementWitness :
    LocalAgreementWitness underivableModel.toSemilocalModel trueAndFrontier :=
  trueAndCertifiedDerivation.toClosedLocalAgreementWitnessOfSemantics
    trueAndCertifiedDerivation_terminal
    trueAndCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    trueAndClosedHintikkaSemantics

def trueAndClosedCountermodel :
    LocalCountermodel (Base := BaseSort) (Const := Const) trueAndFrontier :=
  trueAndCertifiedDerivation.toClosedLocalCountermodelOfSemantics
    trueAndCertifiedDerivation_terminal
    trueAndCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    trueAndClosedHintikkaSemantics

def trueAndClosedSoundCountermodel :
    SoundLocalCountermodel (Base := BaseSort) (Const := Const) trueAndFrontier :=
  trueAndCertifiedDerivation.toClosedSoundLocalCountermodelOfSemantics
    trueAndCertifiedDerivation_terminal
    trueAndCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    trueAndClosedHintikkaSemantics
    underivableSemilocalSupportsUniformRelativization

theorem trueAndCompletion_exists_soundSemantics :
    ∃ (M : SemilocalModel.{0, 0, 0, 0} BaseSort Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      (∀ {φ : Formula Const []},
          (Sign.trueE, φ) ∈ trueAndCompletion.state.hintikka.close.formulas →
            SemilocalModel.formulaTruth M env φ = ⊤) ∧
      (∀ {φ : Formula Const []},
          (Sign.falseE, φ) ∈ trueAndCompletion.state.hintikka.close.formulas →
            SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  refine ⟨underivableModel.toSemilocalModel, underivableEmptyEnv,
    underivableSemilocalGlobal, ?_, ?_, underivableSemilocalSupportsUniformRelativization⟩
  · intro φ hφ
    exact trueAndCertifiedDerivation_true_top <|
      by
        simpa [trueAndCompletion, CertifiedHeadPriorityDerivation.closedHintikka,
          CertifiedHeadPriorityDerivation.hintikka, trueAndCertifiedDerivation_state] using hφ
  · intro φ hφ
    exact trueAndCertifiedDerivation_false_ne_top <|
      by
        simpa [trueAndCompletion, CertifiedHeadPriorityDerivation.closedHintikka,
          CertifiedHeadPriorityDerivation.hintikka, trueAndCertifiedDerivation_state] using hφ

theorem trueAndCompletion_exists_closedLocalAgreementWitness :
    Nonempty
      (Σ M : SemilocalModel.{0, 0, 0, 0} BaseSort Const,
        LocalAgreementWitness M trueAndFrontier) := by
  rcases trueAndCompletion_exists_soundSemantics with
    ⟨M, env, global, true_top, false_ne_top, _⟩
  exact SaturationSearchState.HeadPriorityCompletion.exists_closedLocalAgreementWitness_of_exists_semantics
    (C := trueAndCompletion)
    trueAndFrontier_closedNonconflicting
    trueAndDerivation_compatible
    ⟨M, env, global, true_top, false_ne_top⟩

theorem trueAndCompletion_exists_closedLocalCountermodel :
    Nonempty
      (LocalCountermodel.{0, 0, 0, 0} (Base := BaseSort) (Const := Const) trueAndFrontier) := by
  rcases trueAndCompletion_exists_soundSemantics with
    ⟨M, env, global, true_top, false_ne_top, _⟩
  exact SaturationSearchState.HeadPriorityCompletion.exists_closedLocalCountermodel_of_exists_semantics
    (C := trueAndCompletion)
    trueAndFrontier_closedNonconflicting
    trueAndDerivation_compatible
    ⟨M, env, global, true_top, false_ne_top⟩

theorem trueAndCompletion_not_derivable_via_completion :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      trueAndFrontier.antecedents trueAndFrontier.succedent := by
  exact SaturationSearchState.HeadPriorityCompletion.not_derivable_of_exists_semantics
    (C := trueAndCompletion)
    trueAndFrontier_closedNonconflicting
    trueAndDerivation_compatible
    trueAndCompletion_exists_soundSemantics

theorem trueAndCertifiedDerivation_exists_candidateClosedHintikkaSemantics :
    ∃ (M : SemilocalModel.{0, 0, 0, 0} BaseSort Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
          trueAndCertifiedDerivation
          trueAndCertifiedDerivation_terminal
          trueAndCertifiedDerivation_branchClosed
          env) := by
  refine
    trueAndCertifiedDerivation.exists_candidateClosedHintikkaSemantics_of_exists_semantics
      trueAndCertifiedDerivation_terminal
      trueAndCertifiedDerivation_branchClosed
      ?_
  rcases trueAndCompletion_exists_soundSemantics with
    ⟨M, env, global, true_top, false_ne_top, _⟩
  refine ⟨M, env, global, ?_, ?_⟩
  · intro φ hφ
    exact true_top <|
      by
        simpa [trueAndCompletion, CertifiedHeadPriorityDerivation.closedHintikka,
          CertifiedHeadPriorityDerivation.hintikka, trueAndCertifiedDerivation_state] using hφ
  · intro φ hφ
    exact false_ne_top <|
      by
        simpa [trueAndCompletion, CertifiedHeadPriorityDerivation.closedHintikka,
          CertifiedHeadPriorityDerivation.hintikka, trueAndCertifiedDerivation_state] using hφ

theorem trueAndFrontier_not_derivable :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      trueAndFrontier.antecedents trueAndFrontier.succedent := by
  exact trueAndClosedHintikkaSemantics.not_derivable
    (global := underivableSemilocalGlobal)
    (hM := underivableSemilocalSupportsUniformRelativization)

def mixedOrFormula : Formula Const [] :=
  .or (.bot : Formula Const []) (.top : Formula Const [])

def mixedAndFormula : Formula Const [] :=
  .and mixedOrFormula (.top : Formula Const [])

def mixedFrontier : CompletenessFrontier Const [] :=
  { antecedents := [mixedAndFormula]
    succedent := .bot }

theorem mixedFrontier_closedNonconflicting :
    mixedFrontier.ClosedNonconflicting := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mixedFrontier, mixedAndFormula, mixedOrFormula]

@[simp] theorem mixedInitialAgenda :
    (SaturationSearchState.initial mixedFrontier).agenda = [] := by
  simp [SaturationSearchState.initial, mixedFrontier, mixedAndFormula, mixedOrFormula,
    HintikkaSet.localBranchTargets, LocalBranchTarget.ofSignedFormula]

def mixedProductiveStep :
    SaturationSearchState.ProductiveTriggeredLocalStep
      (SaturationSearchState.initial mixedFrontier) :=
  { step := .trueAnd mixedOrFormula (.top : Formula Const [])
    active := by
      simpa [mixedFrontier, mixedAndFormula, mixedOrFormula]
        using SaturationSearchState.true_mem_initial
          (F := mixedFrontier) (φ := mixedAndFormula)
          (by exact List.mem_singleton_self _)
    fresh := by
      refine ⟨(Sign.trueE, mixedOrFormula), ?_, ?_⟩
      · simp [DeterministicLocalSaturationStep.additions,
          DeterministicLocalSaturationStep.toLocalSaturationStep, LocalSaturationStep.additions,
          mixedOrFormula]
      · intro hmem
        simp [SaturationSearchState.initial, mixedFrontier, mixedAndFormula, mixedOrFormula] at hmem
        rcases hmem with hmem | hmem <;> cases hmem }

def mixedMidState : SaturationSearchState Const [] :=
  { frontier := mixedFrontier
    hintikka :=
      { formulas :=
          [(Sign.trueE, mixedOrFormula),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, mixedAndFormula),
            (Sign.falseE, (.bot : Formula Const []))] }
    agenda := [LocalBranchTarget.trueOr (.bot : Formula Const []) (.top : Formula Const [])] }

@[simp] theorem mixedMidState_formulas :
    mixedMidState.hintikka.formulas =
      [(Sign.trueE, mixedOrFormula),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, mixedAndFormula),
        (Sign.falseE, (.bot : Formula Const []))] := by
  rfl

@[simp] theorem mixedMidState_agenda :
    mixedMidState.agenda =
      [LocalBranchTarget.trueOr (.bot : Formula Const []) (.top : Formula Const [])] := by
  rfl

theorem mixedMidState_eq_applyLocalStep :
    mixedMidState =
      SaturationSearchState.applyLocalStep
        (SaturationSearchState.initial mixedFrontier)
        mixedProductiveStep.step.toLocalSaturationStep := by
  rfl

theorem mixedProductiveStep_compatible :
    (SaturationSearchState.initial mixedFrontier).DeterministicAdditionCompatible
      mixedProductiveStep.step := by
  rw [show mixedProductiveStep.step =
      DeterministicLocalSaturationStep.trueAnd mixedOrFormula (.top : Formula Const []) by
      rfl]
  exact SaturationSearchState.deterministicAdditionCompatible_trueAnd
    (S := SaturationSearchState.initial mixedFrontier)
    (by
      simp [SaturationSearchState.initial, mixedFrontier, mixedAndFormula, mixedOrFormula,
        HintikkaSet.close])
    (by
      simp [SaturationSearchState.initial, mixedFrontier, mixedAndFormula, mixedOrFormula,
        HintikkaSet.close])

def mixedResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .trueOr (.bot : Formula Const []) (.top : Formula Const [])
    step := .trueOrRight (.bot : Formula Const []) (.top : Formula Const [])
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

theorem mixedCanResolveHead :
    mixedMidState.CanResolveHead mixedResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    mixedResolution, mixedMidState]

def mixedState : SaturationSearchState Const [] :=
  { frontier := mixedFrontier
    hintikka :=
      { formulas :=
          [(Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, mixedOrFormula),
            (Sign.trueE, (.top : Formula Const [])),
            (Sign.trueE, mixedAndFormula),
            (Sign.falseE, (.bot : Formula Const []))] }
    agenda := [] }

@[simp] theorem mixedState_formulas :
    mixedState.hintikka.formulas =
      [(Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, mixedOrFormula),
        (Sign.trueE, (.top : Formula Const [])),
        (Sign.trueE, mixedAndFormula),
        (Sign.falseE, (.bot : Formula Const []))] := by
  rfl

theorem mem_mixedState_formulas {sf : SignedFormula Const []} :
    sf ∈ mixedState.hintikka.formulas ↔
      sf = (Sign.trueE, (.top : Formula Const [])) ∨
      sf = (Sign.trueE, mixedOrFormula) ∨
      sf = (Sign.trueE, mixedAndFormula) ∨
      sf = (Sign.falseE, (.bot : Formula Const [])) := by
  constructor <;> intro h
  · simp [mixedState_formulas] at h
    tauto
  · simp [mixedState_formulas] at h ⊢
    tauto

@[simp] theorem mixedState_agenda : mixedState.agenda = [] := by
  rfl

theorem mixedState_eq_resolveHead :
    mixedState = mixedMidState.resolveHead mixedResolution mixedCanResolveHead := by
  rfl

theorem mixedResolution_branchAdditionCompatible :
    mixedMidState.BranchAdditionCompatible mixedResolution := by
  rw [SaturationSearchState.branchAdditionCompatible_trueOrRight_iff
    (S := mixedMidState)
    (r := mixedResolution) (φ := .bot) (ψ := .top) rfl]
  simp [mixedMidState, HintikkaSet.close, mixedOrFormula, mixedAndFormula]

def mixedCertifiedDerivation :
    CertifiedHeadPriorityDerivation Const [] mixedFrontier :=
  CertifiedHeadPriorityDerivation.ofInitialSaturateThenResolveHead
    (Const := Const) (Γ := [])
    mixedFrontier_closedNonconflicting
    mixedInitialAgenda
    mixedProductiveStep
    mixedResolution
    (by simpa [mixedMidState_eq_applyLocalStep] using mixedCanResolveHead)
    mixedProductiveStep_compatible
    (by
      intro sf hsf
      simpa [mixedMidState_eq_applyLocalStep] using
        (mixedResolution_branchAdditionCompatible hsf))

@[simp] theorem mixedCertifiedDerivation_state :
    mixedCertifiedDerivation.state = mixedState := by
  simpa [mixedCertifiedDerivation,
    CertifiedHeadPriorityDerivation.ofInitialSaturateThenResolveHead,
    CertifiedHeadPriorityDerivation.saturate,
    CertifiedHeadPriorityDerivation.resolveHead,
    CertifiedHeadPriorityDerivation.initial,
    mixedMidState_eq_applyLocalStep] using mixedState_eq_resolveHead

theorem mixedState_noProductiveTriggeredStep :
    mixedState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_mixedState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise,
        mixedAndFormula] at hs'
      rcases hs' with h | h | h | h
      · cases h
      · cases h
      · cases h
        rcases hfresh with ⟨sf, hsf, hnot⟩
        have hmem : sf ∈ mixedState.hintikka.formulas := by
          simp [DeterministicLocalSaturationStep.additions,
            DeterministicLocalSaturationStep.toLocalSaturationStep,
            LocalSaturationStep.additions, mixedState_formulas,
            mixedOrFormula] at hsf ⊢
          rcases hsf with hsf | hsf
          · exact Or.inr (Or.inl hsf)
          · exact Or.inl hsf
        exact hnot hmem
      · cases h
  | falseOr φ ψ =>
      have hs' := mem_mixedState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_mixedState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_mixedState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_mixedState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_mixedState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h | h | h <;> cases h

theorem mixedState_branchClosed :
    mixedState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_mixedState_formulas.mp hprem
      rcases hprem' with h | h | h | h <;> cases h
  | trueOr φ ψ =>
      refine ⟨.trueOrRight φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_mixedState_formulas.mp hprem
      rcases hprem' with h | h | h | h
      · cases h
      · cases h
        exact (mem_mixedState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
      · cases h
      · cases h

theorem mixedState_terminal : mixedState.IsTerminal := by
  exact ⟨mixedState_agenda, mixedState_noProductiveTriggeredStep⟩

theorem mixedCertifiedDerivation_terminal :
    mixedCertifiedDerivation.state.IsTerminal := by
  simpa [mixedMidState_eq_applyLocalStep, mixedState_eq_resolveHead] using mixedState_terminal

theorem mixedCertifiedDerivation_branchClosed :
    mixedCertifiedDerivation.state.hintikka.BranchClosed := by
  simpa [mixedMidState_eq_applyLocalStep, mixedState_eq_resolveHead] using mixedState_branchClosed

def mixedCertifiedCompletion :
    CertifiedHeadPriorityCompletion Const [] mixedFrontier :=
  mixedCertifiedDerivation.toCertifiedCompletion
    mixedCertifiedDerivation_terminal
    mixedCertifiedDerivation_branchClosed

def mixedCertifiedCandidate : CertifiedCountermodelCandidate Const [] :=
  mixedCertifiedDerivation.toCertifiedCountermodelCandidate
    mixedCertifiedDerivation_terminal
    mixedCertifiedDerivation_branchClosed

theorem mixedCandidate_closedHintikka_noncontradictory :
    mixedCertifiedCandidate.candidate.closedHintikka.Noncontradictory := by
  exact mixedCertifiedCandidate.closedHintikka_noncontradictory

def mixedClosedCertificate : LocalHintikkaCertificate mixedFrontier :=
  mixedCertifiedDerivation.toClosedLocalHintikkaCertificate
    mixedCertifiedDerivation_terminal
    mixedCertifiedDerivation_branchClosed

theorem mixedCandidate_closedHintikka_true_mem_iff
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ mixedCertifiedCandidate.closedHintikka.formulas ↔
      φ = (.top : Formula Const []) ∨
      φ = mixedOrFormula ∨
      φ = mixedAndFormula := by
  constructor
  · intro h
    have h' : φ = (.top : Formula Const []) ∨ φ = mixedOrFormula ∨
        φ = (.top : Formula Const []) ∨ φ = mixedAndFormula := by
      simpa [mixedCertifiedCandidate, CertifiedHeadPriorityDerivation.closedHintikka,
        CertifiedHeadPriorityDerivation.hintikka, mixedCertifiedDerivation_state,
        mem_mixedState_formulas, HintikkaSet.close, mixedOrFormula, mixedAndFormula] using h
    tauto
  · intro h
    have h' : φ = (.top : Formula Const []) ∨ φ = mixedOrFormula ∨
        φ = (.top : Formula Const []) ∨ φ = mixedAndFormula := by
      tauto
    simpa [mixedCertifiedCandidate, CertifiedHeadPriorityDerivation.closedHintikka,
      CertifiedHeadPriorityDerivation.hintikka, mixedCertifiedDerivation_state,
      mem_mixedState_formulas, HintikkaSet.close, mixedOrFormula, mixedAndFormula] using h'

theorem mixedCandidate_closedHintikka_false_mem_iff_bot
    {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ mixedCertifiedCandidate.closedHintikka.formulas ↔
      φ = (.bot : Formula Const []) := by
  simp [mixedCertifiedCandidate, CertifiedHeadPriorityDerivation.closedHintikka,
    CertifiedHeadPriorityDerivation.hintikka, mixedCertifiedDerivation_state,
    HintikkaSet.close, mixedOrFormula, mixedAndFormula]

def mixedClosedHintikkaSemantics :
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      mixedCertifiedDerivation
      mixedCertifiedDerivation_terminal
      mixedCertifiedDerivation_branchClosed
      underivableEmptyEnv :=
  { trueClass := fun ψ =>
      ψ = (.top : Formula Const []) ∨
        ψ = mixedOrFormula ∨
        ψ = mixedAndFormula
    falseClass := fun ψ => ψ = (.bot : Formula Const [])
    candidate_true_class := by
      intro φ hφ
      exact mixedCandidate_closedHintikka_true_mem_iff.mp hφ
    candidate_false_class := by
      intro φ hφ
      exact mixedCandidate_closedHintikka_false_mem_iff_bot.mp hφ
    true_top_of_class := by
      intro φ hφ
      rcases hφ with rfl | rfl | rfl
      · simp
      · simp [mixedOrFormula]
      · simp [mixedAndFormula, mixedOrFormula]
    false_ne_top_of_class := by
      intro φ hφ
      subst hφ
      intro h
      simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h }

theorem mixedCertifiedDerivation_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ mixedCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  exact mixedClosedHintikkaSemantics.closedHintikka_true_top hφ

theorem mixedCertifiedDerivation_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ mixedCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  exact mixedClosedHintikkaSemantics.closedHintikka_false_ne_top hφ

theorem mixedClosed_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ mixedCertifiedCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  rcases mixedCandidate_closedHintikka_true_mem_iff.mp hφ with rfl | rfl | rfl
  · simp
  · simp [mixedOrFormula]
  · simp [mixedAndFormula, mixedOrFormula]

theorem mixedClosed_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ mixedCertifiedCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  have hBot : φ = (.bot : Formula Const []) :=
    mixedCandidate_closedHintikka_false_mem_iff_bot.mp hφ
  subst hBot
  intro h
  simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h

def mixedClosedAgreementWitness :
    LocalAgreementWitness underivableModel.toSemilocalModel mixedFrontier :=
  mixedCertifiedDerivation.toClosedLocalAgreementWitnessOfSemantics
    mixedCertifiedDerivation_terminal
    mixedCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    mixedClosedHintikkaSemantics

def mixedClosedCountermodel :
    LocalCountermodel (Base := BaseSort) (Const := Const) mixedFrontier :=
  mixedCertifiedDerivation.toClosedLocalCountermodelOfSemantics
    mixedCertifiedDerivation_terminal
    mixedCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    mixedClosedHintikkaSemantics

def mixedClosedSoundCountermodel :
    SoundLocalCountermodel (Base := BaseSort) (Const := Const) mixedFrontier :=
  mixedCertifiedDerivation.toClosedSoundLocalCountermodelOfSemantics
    mixedCertifiedDerivation_terminal
    mixedCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    mixedClosedHintikkaSemantics
    underivableSemilocalSupportsUniformRelativization

theorem mixedFrontier_not_derivable :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      mixedFrontier.antecedents mixedFrontier.succedent := by
  exact mixedClosedHintikkaSemantics.not_derivable
    (global := underivableSemilocalGlobal)
    (hM := underivableSemilocalSupportsUniformRelativization)

def falseAndFrontier : CompletenessFrontier Const [] :=
  { antecedents := []
    succedent := .and (.bot : Formula Const []) (.top : Formula Const []) }

theorem falseAndFrontier_closedNonconflicting :
    falseAndFrontier.ClosedNonconflicting := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [falseAndFrontier]

def falseAndResolution : SaturationSearchState.LocalBranchResolution Const [] :=
  { target := .falseAnd (.bot : Formula Const []) (.top : Formula Const [])
    step := .falseAndLeft (.bot : Formula Const []) (.top : Formula Const [])
    admissible := by
      simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches] }

@[simp] theorem falseAndInitialAgenda :
    (SaturationSearchState.initial falseAndFrontier).agenda =
      [LocalBranchTarget.falseAnd (.bot : Formula Const []) (.top : Formula Const [])] := by
  simp [SaturationSearchState.initial, falseAndFrontier, HintikkaSet.localBranchTargets,
    LocalBranchTarget.ofSignedFormula]

theorem falseAndCanResolveHead :
    (SaturationSearchState.initial falseAndFrontier).CanResolveHead falseAndResolution := by
  simp [SaturationSearchState.CanResolveHead, SaturationSearchState.nextAgendaTarget?,
    falseAndResolution]

def falseAndState : SaturationSearchState Const [] :=
  { frontier := falseAndFrontier
    hintikka :=
      { formulas :=
          [(Sign.falseE, (.bot : Formula Const [])),
            (Sign.falseE, (.and (.bot : Formula Const []) (.top : Formula Const [])))] }
    agenda := [] }

@[simp] theorem falseAndState_formulas :
    falseAndState.hintikka.formulas =
      [(Sign.falseE, (.bot : Formula Const [])),
        (Sign.falseE, (.and (.bot : Formula Const []) (.top : Formula Const [])))] := by
  rfl

theorem mem_falseAndState_formulas {sf : SignedFormula Const []} :
    sf ∈ falseAndState.hintikka.formulas ↔
      sf = (Sign.falseE, (.bot : Formula Const [])) ∨
      sf = (Sign.falseE, (.and (.bot : Formula Const []) (.top : Formula Const []))) := by
  simp [falseAndState_formulas]

@[simp] theorem falseAndState_agenda : falseAndState.agenda = [] := by
  rfl

theorem falseAndState_eq_resolveHead :
    falseAndState =
      (SaturationSearchState.initial falseAndFrontier).resolveHead
        falseAndResolution falseAndCanResolveHead := by
  rfl

theorem falseAndState_noProductiveTriggeredStep :
    falseAndState.NoProductiveTriggeredStep := by
  intro t
  rcases t with ⟨s, hs, hfresh⟩
  cases s with
  | trueAnd φ ψ =>
      have hs' := mem_falseAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h <;> cases h
  | falseOr φ ψ =>
      have hs' := mem_falseAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h <;> cases h
  | trueAll φ t =>
      have hs' := mem_falseAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h <;> cases h
  | falseAllWitness φ t =>
      have hs' := mem_falseAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h <;> cases h
  | trueExWitness φ t =>
      have hs' := mem_falseAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h <;> cases h
  | falseEx φ t =>
      have hs' := mem_falseAndState_formulas.mp hs
      simp [DeterministicLocalSaturationStep.premise, LocalSaturationStep.premise] at hs'
      rcases hs' with h | h <;> cases h

theorem falseAndState_branchClosed :
    falseAndState.hintikka.BranchClosed := by
  intro b
  cases b with
  | falseAnd φ ψ =>
      refine ⟨.falseAndLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem sf hsf
      have hprem' := mem_falseAndState_formulas.mp hprem
      rcases hprem' with h | h
      · cases h
      · cases h
        exact (mem_falseAndState_formulas).2 <|
          Or.inl (by simpa [LocalSaturationStep.additions] using hsf)
  | trueOr φ ψ =>
      refine ⟨.trueOrLeft φ ψ, by simp [LocalBranchTarget.AcceptsStep, LocalBranchTarget.branches], ?_⟩
      intro hprem
      have hprem' := mem_falseAndState_formulas.mp hprem
      rcases hprem' with h | h <;> cases h

theorem falseAndState_terminal : falseAndState.IsTerminal := by
  exact ⟨falseAndState_agenda, falseAndState_noProductiveTriggeredStep⟩

def falseAndDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation falseAndFrontier falseAndState :=
  by
    simpa [falseAndState_eq_resolveHead] using
      (SaturationSearchState.HeadPrioritySearchDerivation.resolveHead
        (F := falseAndFrontier)
        SaturationSearchState.HeadPrioritySearchDerivation.initial
        falseAndResolution falseAndCanResolveHead)

def falseAndCompletion : SaturationSearchState.HeadPriorityCompletion falseAndFrontier :=
  { state := falseAndState
    derivation := falseAndDerivation
    terminal := falseAndState_terminal
    branchClosed := falseAndState_branchClosed }

def falseAndCandidate : CountermodelCandidate Const [] :=
  { frontier := falseAndFrontier
    completion := falseAndCompletion }

theorem falseAndInitialClosedHintikka_trueBot_not_mem :
    (Sign.trueE, (.bot : Formula Const [])) ∉
      (SaturationSearchState.initial falseAndFrontier).hintikka.close.formulas := by
  simp [SaturationSearchState.initial, falseAndFrontier, HintikkaSet.close]

theorem falseAndResolution_branchAdditionCompatible :
    (SaturationSearchState.initial falseAndFrontier).BranchAdditionCompatible falseAndResolution := by
  rw [SaturationSearchState.branchAdditionCompatible_falseAndLeft_iff
    (S := SaturationSearchState.initial falseAndFrontier)
    (r := falseAndResolution) (φ := .bot) (ψ := .top) rfl]
  simpa [SignedFormula.flip] using falseAndInitialClosedHintikka_trueBot_not_mem

theorem falseAndDerivation_compatible :
    SaturationSearchState.HeadPrioritySearchDerivation.Compatible falseAndDerivation := by
  simpa [falseAndDerivation, falseAndState_eq_resolveHead,
    SaturationSearchState.HeadPrioritySearchDerivation.Compatible] using
    SaturationSearchState.HeadPrioritySearchDerivation.compatible_resolveHead
      (D := SaturationSearchState.HeadPrioritySearchDerivation.initial (F := falseAndFrontier))
      (r := falseAndResolution)
      (hhead := falseAndCanResolveHead)
      (by
        exact SaturationSearchState.HeadPrioritySearchDerivation.compatible_initial)
      falseAndResolution_branchAdditionCompatible

def falseAndCertifiedDerivation :
    CertifiedHeadPriorityDerivation Const [] falseAndFrontier :=
  CertifiedHeadPriorityDerivation.ofInitialResolveHead
    (Const := Const) (Γ := [])
    falseAndFrontier_closedNonconflicting
    falseAndResolution
    falseAndCanResolveHead
    falseAndResolution_branchAdditionCompatible

@[simp] theorem falseAndCertifiedDerivation_state :
    falseAndCertifiedDerivation.state = falseAndState := by
  simpa [falseAndCertifiedDerivation, CertifiedHeadPriorityDerivation.ofInitialResolveHead,
    CertifiedHeadPriorityDerivation.resolveHead, CertifiedHeadPriorityDerivation.initial] using
    falseAndState_eq_resolveHead

theorem falseAndCertifiedDerivation_terminal :
    falseAndCertifiedDerivation.state.IsTerminal := by
  simpa using falseAndState_terminal

theorem falseAndCertifiedDerivation_branchClosed :
    falseAndCertifiedDerivation.state.hintikka.BranchClosed := by
  simpa using falseAndState_branchClosed

theorem falseAndCertifiedDerivation_closedHintikka_noncontradictory :
    falseAndCertifiedDerivation.state.hintikka.close.Noncontradictory := by
  exact falseAndCertifiedDerivation.closedHintikka_noncontradictory

def falseAndCertifiedCompletion :
    CertifiedHeadPriorityCompletion Const [] falseAndFrontier :=
  falseAndCertifiedDerivation.toCertifiedCompletion
    falseAndCertifiedDerivation_terminal
    falseAndCertifiedDerivation_branchClosed

def falseAndCertifiedCandidate : CertifiedCountermodelCandidate Const [] :=
  falseAndCertifiedDerivation.toCertifiedCountermodelCandidate
    falseAndCertifiedDerivation_terminal
    falseAndCertifiedDerivation_branchClosed

theorem falseAndCandidate_closedHintikka_noncontradictory :
    falseAndCandidate.closedHintikka.Noncontradictory := by
  exact falseAndCertifiedCandidate.closedHintikka_noncontradictory

def falseAndClosedCertificate : LocalHintikkaCertificate falseAndFrontier :=
  falseAndCertifiedDerivation.toClosedLocalHintikkaCertificate
    falseAndCertifiedDerivation_terminal
    falseAndCertifiedDerivation_branchClosed

theorem falseAndCandidate_closedHintikka_true_mem_iff_top
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ falseAndCertifiedCandidate.closedHintikka.formulas ↔
      φ = (.top : Formula Const []) := by
  simp [falseAndCertifiedCandidate, CertifiedHeadPriorityDerivation.closedHintikka,
    CertifiedHeadPriorityDerivation.hintikka, falseAndCertifiedDerivation_state,
    falseAndState_formulas, HintikkaSet.close]

theorem falseAndCandidate_closedHintikka_false_mem_iff
    {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ falseAndCertifiedCandidate.closedHintikka.formulas ↔
      φ = (.bot : Formula Const []) ∨
        φ = (.and (.bot : Formula Const []) (.top : Formula Const [])) := by
  constructor
  · intro h
    have h' :
        φ = (.bot : Formula Const []) ∨
          φ = (.bot : Formula Const []) ∨
          φ = (.and (.bot : Formula Const []) (.top : Formula Const [])) := by
      simp [falseAndCertifiedCandidate, CertifiedHeadPriorityDerivation.closedHintikka,
        CertifiedHeadPriorityDerivation.hintikka, falseAndCertifiedDerivation_state,
        falseAndState_formulas, HintikkaSet.close] at h ⊢
      exact h
    tauto
  · intro h
    have h' :
        φ = (.bot : Formula Const []) ∨
          φ = (.bot : Formula Const []) ∨
          φ = (.and (.bot : Formula Const []) (.top : Formula Const [])) := by
      tauto
    simp [falseAndCertifiedCandidate, CertifiedHeadPriorityDerivation.closedHintikka,
      CertifiedHeadPriorityDerivation.hintikka, falseAndCertifiedDerivation_state,
      falseAndState_formulas, HintikkaSet.close] at h' ⊢
    exact h'

def falseAndClosedHintikkaSemantics :
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      falseAndCertifiedDerivation
      falseAndCertifiedDerivation_terminal
      falseAndCertifiedDerivation_branchClosed
      underivableEmptyEnv :=
  { trueClass := fun ψ => ψ = (.top : Formula Const [])
    falseClass := fun ψ =>
      ψ = (.bot : Formula Const []) ∨
        ψ = (.and (.bot : Formula Const []) (.top : Formula Const []))
    candidate_true_class := by
      intro φ hφ
      exact falseAndCandidate_closedHintikka_true_mem_iff_top.mp hφ
    candidate_false_class := by
      intro φ hφ
      exact falseAndCandidate_closedHintikka_false_mem_iff.mp hφ
    true_top_of_class := by
      intro φ hφ
      subst hφ
      simp
    false_ne_top_of_class := by
      intro φ hφ
      rcases hφ with rfl | rfl
      · intro h
        simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h
      · intro h
        simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h }

theorem falseAndCertifiedDerivation_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ falseAndCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  exact falseAndClosedHintikkaSemantics.closedHintikka_true_top hφ

theorem falseAndCertifiedDerivation_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ falseAndCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  exact falseAndClosedHintikkaSemantics.closedHintikka_false_ne_top hφ

theorem falseAndClosed_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ falseAndCertifiedCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  have hTop : φ = (.top : Formula Const []) :=
    falseAndCandidate_closedHintikka_true_mem_iff_top.mp hφ
  subst hTop
  simp

theorem falseAndClosed_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ falseAndCertifiedCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  rcases falseAndCandidate_closedHintikka_false_mem_iff.mp hφ with rfl | rfl
  · intro h
    simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h
  · intro h
    simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h

def falseAndClosedAgreementWitness :
    LocalAgreementWitness underivableModel.toSemilocalModel falseAndFrontier :=
  falseAndCertifiedDerivation.toClosedLocalAgreementWitnessOfSemantics
    falseAndCertifiedDerivation_terminal
    falseAndCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    falseAndClosedHintikkaSemantics

def falseAndClosedCountermodel :
    LocalCountermodel (Base := BaseSort) (Const := Const) falseAndFrontier :=
  falseAndCertifiedDerivation.toClosedLocalCountermodelOfSemantics
    falseAndCertifiedDerivation_terminal
    falseAndCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    falseAndClosedHintikkaSemantics

def falseAndClosedSoundCountermodel :
    SoundLocalCountermodel (Base := BaseSort) (Const := Const) falseAndFrontier :=
  falseAndCertifiedDerivation.toClosedSoundLocalCountermodelOfSemantics
    falseAndCertifiedDerivation_terminal
    falseAndCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    falseAndClosedHintikkaSemantics
    underivableSemilocalSupportsUniformRelativization

theorem falseAndFrontier_not_derivable :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      falseAndFrontier.antecedents falseAndFrontier.succedent := by
  exact falseAndClosedHintikkaSemantics.not_derivable
    (global := underivableSemilocalGlobal)
    (hM := underivableSemilocalSupportsUniformRelativization)

theorem deterministicState_closedHintikka_contradictory :
    deterministicState.hintikka.close.Contradictory := by
  apply HintikkaSet.contradictory_of_conflict
  · exact HintikkaSet.mem_close_of_mem <|
      SaturationSearchState.mem_applyLocalStep_of_addition
        (S := SaturationSearchState.initial deterministicFrontier)
        (s := deterministicProductiveStep.step.toLocalSaturationStep)
        (show
          (Sign.trueE, deterministicWitnessFormula) ∈
            LocalSaturationStep.additions deterministicProductiveStep.step.toLocalSaturationStep by
          simp [deterministicProductiveStep, DeterministicLocalSaturationStep.toLocalSaturationStep,
            LocalSaturationStep.additions, deterministicWitnessFormula])
  · exact HintikkaSet.mem_close_of_mem <|
      SaturationSearchState.mem_applyLocalStep_of_mem
        (S := SaturationSearchState.initial deterministicFrontier)
        (s := deterministicProductiveStep.step.toLocalSaturationStep)
        (SaturationSearchState.false_mem_initial deterministicFrontier)

def deterministicDerivation :
    SaturationSearchState.HeadPrioritySearchDerivation deterministicFrontier deterministicState := by
  simpa [deterministicState_eq_applyLocalStep] using
    (SaturationSearchState.HeadPrioritySearchDerivation.saturate
      (F := deterministicFrontier)
      SaturationSearchState.HeadPrioritySearchDerivation.initial
      deterministicInitialAgenda
      deterministicProductiveStep)

theorem deterministicDerivation_not_compatible :
    ¬ SaturationSearchState.HeadPrioritySearchDerivation.Compatible deterministicDerivation := by
  intro hCompat
  have hNoncontradictory :=
    SaturationSearchState.HeadPrioritySearchDerivation.closed_noncontradictory
      deterministicDerivation
      deterministicInitialClosedHintikka_noncontradictory
      hCompat
  exact hNoncontradictory deterministicState_closedHintikka_contradictory

theorem deterministicCandidate_closedHintikka_contradictory
    (C : CountermodelCandidate Const [])
    (hFrontier : C.frontier = deterministicFrontier) :
    C.closedHintikka.Contradictory := by
  have hTrueTrigger :
      (Sign.trueE, deterministicTriggerFormula) ∈ C.hintikka.formulas := by
    exact C.true_mem (by simp [hFrontier, deterministicFrontier])
  have hTrueWitness :
      (Sign.trueE, deterministicWitnessFormula) ∈ C.hintikka.formulas := by
    exact (HintikkaSet.trueAnd_mem_of_locallySaturated
      C.locallySaturated hTrueTrigger).1
  have hFalseWitness :
      (Sign.falseE, deterministicWitnessFormula) ∈ C.hintikka.formulas := by
    simpa [hFrontier, deterministicFrontier] using C.false_mem
  exact HintikkaSet.contradictory_of_conflict
    (HintikkaSet.mem_close_of_mem hTrueWitness)
    (HintikkaSet.mem_close_of_mem hFalseWitness)

theorem deterministicCandidate_closedHintikka_not_noncontradictory
    (C : CountermodelCandidate Const [])
    (hFrontier : C.frontier = deterministicFrontier) :
    ¬ C.closedHintikka.Noncontradictory := by
  intro hNoncontradictory
  exact hNoncontradictory
    (deterministicCandidate_closedHintikka_contradictory C hFrontier)

theorem noCertifiedCandidate_deterministicFrontier :
    ¬ ∃ C : CertifiedCountermodelCandidate Const [], C.frontier = deterministicFrontier := by
  rintro ⟨C, hFrontier⟩
  have hNoncontradictory : C.candidate.closedHintikka.Noncontradictory := by
    simpa [CertifiedCountermodelCandidate.closedHintikka] using
      C.closedHintikka_noncontradictory
  exact
    (deterministicCandidate_closedHintikka_not_noncontradictory
      C.candidate (by simpa [CertifiedCountermodelCandidate.frontier] using hFrontier))
      hNoncontradictory

theorem noCertifiedCompletion_deterministicFrontier :
    ¬ Nonempty (CertifiedHeadPriorityCompletion Const [] deterministicFrontier) := by
  rintro ⟨C⟩
  exact noCertifiedCandidate_deterministicFrontier
    ⟨C.toCertifiedCountermodelCandidate, by
      simp [CertifiedHeadPriorityCompletion.toCertifiedCountermodelCandidate,
        CertifiedHeadPriorityCompletion.toCountermodelCandidate,
        CertifiedCountermodelCandidate.frontier]⟩

theorem underivableResolution_not_branchAdditionCompatible :
    ¬ (SaturationSearchState.initial underivableFrontier).BranchAdditionCompatible
      underivableResolution := by
  intro hCompat
  have hNot : SignedFormula.flip (Sign.trueE, (.bot : Formula Const [])) ∉
      (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
    exact hCompat (by simp [underivableResolution, LocalSaturationStep.additions])
  have hFalseBot :
      (Sign.falseE, (.bot : Formula Const [])) ∈
        (SaturationSearchState.initial underivableFrontier).hintikka.close.formulas := by
    exact HintikkaSet.falseBot_mem_close
      ((SaturationSearchState.initial underivableFrontier).hintikka)
  exact hNot hFalseBot

theorem goodCandidate_closedHintikka_false_mem_iff_bot {φ : Formula Const []} :
    (Sign.falseE, φ) ∈ goodCandidate.closedHintikka.formulas ↔
      φ = (.bot : Formula Const []) := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

theorem goodCandidate_closedHintikka_true_mem_iff
    {φ : Formula Const []} :
    (Sign.trueE, φ) ∈ goodCandidate.closedHintikka.formulas ↔
      φ = (.top : Formula Const []) ∨
        φ = (.or (.bot : Formula Const []) (.top : Formula Const [])) := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

theorem goodCandidate_closedHintikka_trueBot_not_mem :
    (Sign.trueE, (.bot : Formula Const [])) ∉ goodCandidate.closedHintikka.formulas := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

theorem goodCandidate_closedHintikka_falseTop_not_mem :
    (Sign.falseE, (.top : Formula Const [])) ∉ goodCandidate.closedHintikka.formulas := by
  simp [goodCandidate, CountermodelCandidate.closedHintikka, CountermodelCandidate.hintikka,
    CountermodelCandidate.state, goodCompletion, goodState_formulas, HintikkaSet.close]

def goodCertifiedDerivation :
    CertifiedHeadPriorityDerivation Const [] underivableFrontier :=
  CertifiedHeadPriorityDerivation.ofInitialResolveHead
    (Const := Const) (Γ := [])
    underivableFrontier_closedNonconflicting
    goodResolution
    goodCanResolveHead
    goodResolution_branchAdditionCompatible

@[simp] theorem goodCertifiedDerivation_state :
    goodCertifiedDerivation.state = goodState := by
  simpa [goodCertifiedDerivation, CertifiedHeadPriorityDerivation.ofInitialResolveHead,
    CertifiedHeadPriorityDerivation.resolveHead, CertifiedHeadPriorityDerivation.initial] using
    goodState_eq_resolveHead

theorem goodCertifiedDerivation_terminal :
    goodCertifiedDerivation.state.IsTerminal := by
  simpa [goodCertifiedDerivation_state] using goodState_terminal

theorem goodCertifiedDerivation_branchClosed :
    goodCertifiedDerivation.state.hintikka.BranchClosed := by
  simpa [goodCertifiedDerivation_state] using goodState_branchClosed

theorem goodCertifiedDerivation_closedHintikka_noncontradictory :
    goodCertifiedDerivation.closedHintikka.Noncontradictory := by
  exact goodCertifiedDerivation.closedHintikka_noncontradictory

def goodClosedHintikkaSemantics :
    CertifiedHeadPriorityDerivation.CandidateClosedHintikkaSemantics
      goodCertifiedDerivation
      goodCertifiedDerivation_terminal
      goodCertifiedDerivation_branchClosed
      underivableEmptyEnv :=
  { trueClass := fun ψ =>
      ψ = (.top : Formula Const []) ∨
        ψ = (.or (.bot : Formula Const []) (.top : Formula Const []))
    falseClass := fun ψ => ψ = (.bot : Formula Const [])
    candidate_true_class := by
      intro φ hφ
      exact goodCandidate_closedHintikka_true_mem_iff.mp hφ
    candidate_false_class := by
      intro φ hφ
      exact goodCandidate_closedHintikka_false_mem_iff_bot.mp hφ
    true_top_of_class := by
      intro φ hφ
      rcases hφ with rfl | rfl <;> simp
    false_ne_top_of_class := by
      intro φ hφ
      subst hφ
      intro h
      simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h }

theorem goodCertifiedDerivation_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ goodCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  exact goodClosedHintikkaSemantics.closedHintikka_true_top hφ

theorem goodCertifiedDerivation_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ goodCertifiedDerivation.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  exact goodClosedHintikkaSemantics.closedHintikka_false_ne_top hφ

def goodCertifiedCompletion :
    CertifiedHeadPriorityCompletion Const [] underivableFrontier :=
  goodCertifiedDerivation.toCertifiedCompletion
    goodCertifiedDerivation_terminal
    goodCertifiedDerivation_branchClosed

def goodCertifiedCandidate : CertifiedCountermodelCandidate Const [] :=
  goodCertifiedDerivation.toCertifiedCountermodelCandidate
    goodCertifiedDerivation_terminal
    goodCertifiedDerivation_branchClosed

theorem goodCandidate_closedHintikka_noncontradictory :
    goodCandidate.closedHintikka.Noncontradictory := by
  exact goodCertifiedCandidate.closedHintikka_noncontradictory

def goodClosedCertificate : LocalHintikkaCertificate underivableFrontier :=
  goodCertifiedDerivation.toClosedLocalHintikkaCertificate
    goodCertifiedDerivation_terminal
    goodCertifiedDerivation_branchClosed

theorem goodClosed_true_top
    {φ : Formula Const []}
    (hφ : (Sign.trueE, φ) ∈ goodCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ = ⊤ := by
  rcases goodCandidate_closedHintikka_true_mem_iff.mp hφ with rfl | rfl
  · simp
  · simp

theorem goodClosed_false_ne_top
    {φ : Formula Const []}
    (hφ : (Sign.falseE, φ) ∈ goodCandidate.closedHintikka.formulas) :
    SemilocalModel.formulaTruth underivableModel.toSemilocalModel underivableEmptyEnv φ ≠ ⊤ := by
  have hBot : φ = (.bot : Formula Const []) :=
    goodCandidate_closedHintikka_false_mem_iff_bot.mp hφ
  subst hBot
  intro h
  simp [underivableModel, SemilocalModel.formulaTruth, SemilocalModel.eval] at h

def goodClosedAgreementWitness :
    LocalAgreementWitness underivableModel.toSemilocalModel underivableFrontier :=
  goodCertifiedDerivation.toClosedLocalAgreementWitnessOfSemantics
    goodCertifiedDerivation_terminal
    goodCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    goodClosedHintikkaSemantics

def goodClosedCountermodel :
    LocalCountermodel (Base := BaseSort) (Const := Const) underivableFrontier :=
  goodCertifiedDerivation.toClosedLocalCountermodelOfSemantics
    goodCertifiedDerivation_terminal
    goodCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    goodClosedHintikkaSemantics

def goodClosedSoundCountermodel :
    SoundLocalCountermodel (Base := BaseSort) (Const := Const) underivableFrontier :=
  goodCertifiedDerivation.toClosedSoundLocalCountermodelOfSemantics
    goodCertifiedDerivation_terminal
    goodCertifiedDerivation_branchClosed
    underivableEmptyEnv
    underivableSemilocalGlobal
    goodClosedHintikkaSemantics
    underivableSemilocalSupportsUniformRelativization

def goodCompletionClosedHintikkaSemantics :
    CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
      goodCertifiedCompletion underivableEmptyEnv := by
  simpa [CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics,
    goodCertifiedCompletion, CertifiedHeadPriorityDerivation.toCertifiedCompletion,
    CertifiedHeadPriorityCompletion.ofCertifiedDerivation,
    CertifiedHeadPriorityCompletion.toCertifiedDerivation] using
    goodClosedHintikkaSemantics

def goodCompletionAgreementWitness :
    LocalAgreementWitness underivableModel.toSemilocalModel underivableFrontier :=
  goodCertifiedCompletion.toClosedLocalAgreementWitnessOfSemantics
    underivableEmptyEnv
    underivableSemilocalGlobal
    goodCompletionClosedHintikkaSemantics

theorem goodCompletionAgreementWitness_certificate :
    goodCompletionAgreementWitness.certificate =
      goodCertifiedCompletion.toClosedLocalHintikkaCertificate := by
  simp [goodCompletionAgreementWitness]

theorem goodCertifiedCompletion_exists_candidateClosedHintikkaSemantics :
    ∃ (M : SemilocalModel.{0, 0, 0, 0} BaseSort Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
          goodCertifiedCompletion env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  refine ⟨underivableModel.toSemilocalModel, underivableEmptyEnv,
    underivableSemilocalGlobal, ⟨goodCompletionClosedHintikkaSemantics⟩,
    underivableSemilocalSupportsUniformRelativization⟩

theorem goodCertifiedCompletion_exists_candidateClosedHintikkaSemantics_viaWitness :
    ∃ (M : SemilocalModel.{0, 0, 0, 0} BaseSort Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
          goodCertifiedCompletion env) := by
  refine
    CertifiedHeadPriorityCompletion.exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness
      (C := goodCertifiedCompletion) ?_
  exact ⟨underivableModel.toSemilocalModel, goodCompletionAgreementWitness,
    goodCompletionAgreementWitness_certificate⟩

example :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent :=
  underivableInitialHintikka_icttConsistent

example :
    ¬ underivableCandidate.closedHintikka.ICTTConsistent :=
  underivableCandidate_closedHintikka_not_icttConsistent

example :
    goodCandidate.closedHintikka.Noncontradictory :=
  goodCandidate_closedHintikka_noncontradictory

example :
    LocalHintikkaCertificate underivableFrontier :=
  goodClosedCertificate

example :
    LocalCountermodel (Base := BaseSort) (Const := Const) underivableFrontier :=
  goodClosedCountermodel

example :
    ∃ (M : SemilocalModel.{0, 0, 0, 0} BaseSort Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
          goodCertifiedCompletion env) :=
  goodCertifiedCompletion_exists_candidateClosedHintikkaSemantics_viaWitness

example :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      underivableFrontier.antecedents underivableFrontier.succedent :=
  goodClosedHintikkaSemantics.not_derivable
    (global := underivableSemilocalGlobal)
    (hM := underivableSemilocalSupportsUniformRelativization)

example :
    ¬ Derivable (Base := BaseSort) (Const := Const)
      underivableFrontier.antecedents underivableFrontier.succedent :=
  goodCertifiedCompletion.not_derivable_of_exists_candidateClosedHintikkaSemantics
    goodCertifiedCompletion_exists_candidateClosedHintikkaSemantics

example :
    (SaturationSearchState.initial underivableFrontier).hintikka.ICTTConsistent ∧
      ¬ ((SaturationSearchState.initial underivableFrontier).resolveHead
          underivableResolution underivableCanResolveHead).hintikka.close.ICTTConsistent :=
  underivableResolution_breaks_initial_icttConsistent

end CompletenessRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
