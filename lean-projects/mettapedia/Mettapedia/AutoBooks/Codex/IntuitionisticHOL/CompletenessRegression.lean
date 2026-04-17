import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.KHintikka
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CompletenessRegression

open Mettapedia.Logic.HOL
open KHintikkaPath

inductive BaseSort where
  | atom
  deriving DecidableEq

def Const : Ty BaseSort → Type := fun _ => PEmpty

abbrev ClosedProp := ClosedFormula Const
abbrev Root := Unit
abbrev root : Root := ()

def goodFrontier : CompletenessFrontier Const [] :=
  { antecedents := [(.top : ClosedProp)]
    succedent := (.bot : ClosedProp) }

def badFrontier : CompletenessFrontier Const [] :=
  { antecedents := [(.top : ClosedProp)]
    succedent := (.top : ClosedProp) }

def falseOrPath : KHintikkaPath Root Const :=
  [KSignedFormula.falseAt (Const := Const) root
    (.or (.top : ClosedProp) (.bot : ClosedProp))]

theorem goodFrontier_closedNonconflicting :
    goodFrontier.ClosedNonconflicting := by
  simp [goodFrontier, CompletenessFrontier.ClosedNonconflicting]

theorem badFrontier_not_closedNonconflicting :
    ¬ badFrontier.ClosedNonconflicting := by
  simp [badFrontier, CompletenessFrontier.ClosedNonconflicting]

theorem goodFrontier_initial_close_noncontradictory :
    goodFrontier.initialHintikkaSet.close.Noncontradictory := by
  exact
    (CompletenessFrontier.initialHintikkaSet_close_noncontradictory_iff
      (F := goodFrontier)).2 goodFrontier_closedNonconflicting

theorem badFrontier_initial_close_not_noncontradictory :
    ¬ badFrontier.initialHintikkaSet.close.Noncontradictory := by
  intro h
  exact badFrontier_not_closedNonconflicting <|
    (CompletenessFrontier.initialHintikkaSet_close_noncontradictory_iff
      (F := badFrontier)).1 h

theorem goodFrontier_initial_hintikka_eq_initialHintikkaSet :
    (SaturationSearchState.initial goodFrontier).hintikka = goodFrontier.initialHintikkaSet := by
  exact
    (CompletenessFrontier.initial_hintikka_eq_initialHintikkaSet (F := goodFrontier))

theorem goodFrontier_kpath_forGoal :
    (ofHintikkaGoal (Base := BaseSort) (Const := Const) root goodFrontier.toHintikkaGoal).ForGoal
      root goodFrontier.antecedents goodFrontier.succedent := by
  simpa [goodFrontier, CompletenessFrontier.toHintikkaGoal] using
    (forGoal_ofHintikkaGoal (Base := BaseSort) (Const := Const) root goodFrontier.toHintikkaGoal)

theorem goodFrontier_kpath_positiveAt_root :
    (ofHintikkaGoal (Base := BaseSort) (Const := Const) root goodFrontier.toHintikkaGoal).positiveAt root =
      goodFrontier.antecedents := by
  simp [KHintikkaPath.ofHintikkaGoal, goodFrontier, CompletenessFrontier.toHintikkaGoal]

theorem goodFrontier_kpath_negativeAt_root :
    (ofHintikkaGoal (Base := BaseSort) (Const := Const) root goodFrontier.toHintikkaGoal).negativeAt root =
      [goodFrontier.succedent] := by
  simp [KHintikkaPath.ofHintikkaGoal, goodFrontier, CompletenessFrontier.toHintikkaGoal]

theorem falseOrPath_positiveAt_root :
    falseOrPath.positiveAt root = [] := by
  simp [falseOrPath, KHintikkaPath.positiveAt, KSignedFormula.falseAt]

theorem falseOrPath_negativeAt_root :
    falseOrPath.negativeAt root = [.or (.top : ClosedProp) (.bot : ClosedProp)] := by
  simp [falseOrPath, KHintikkaPath.negativeAt, KSignedFormula.falseAt]

theorem falseOrPath_negativeAt_after_extendFalseOr :
    (falseOrPath.extendFalseOr root (.top : ClosedProp) (.bot : ClosedProp)).negativeAt root =
      [.or (.top : ClosedProp) (.bot : ClosedProp), (.top : ClosedProp), (.bot : ClosedProp)] := by
  simp [falseOrPath, KHintikkaPath.extendFalseOr, KHintikkaPath.negativeAt,
    KSignedFormula.falseAt]

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CompletenessRegression
