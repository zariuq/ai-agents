import Foet.EthicsCore

set_option autoImplicit false

namespace Foet

universe u

/-!
“Standard paradigms” at the meta-ethics level, Lean-first.

Key idea: instead of SUMO axioms saying “a deontological theory is a set whose
elements are deontological sentences”, we *make it a type*:

`DeontologicalImperativeTheory World := Theory (DeonticSentence World)`

That is the plumbing win: ill-typed mixtures are unrepresentable.
-/

/-- Deontology (imperative/deontic) as “a set of deontic sentences”. -/
abbrev DeontologicalImperativeTheory (World : Type u) : Type (max u 1) :=
  Theory (DeonticSentence World)

-- The value-judgment paradigm is already `ValueJudgmentTheory` in `Foet.EthicsCore`.

/-- Comparators for utility values (mirrors KIF: >, <, ≥, ≤, =). -/
inductive UtilityComparator : Type
  | lt
  | le
  | gt
  | ge
  | eq
  deriving DecidableEq, Repr

/--
Minimal utilitarian sentence forms.

We keep `UtilityFn` symbolic (uninterpreted) so different models can interpret it differently.
-/
inductive UtilitarianSentence (World : Type u) (Utility : Type u) (UtilityFn : Type u) : Type (max u 1)
  | assign (uf : UtilityFn) (φ : Formula World) (value : Utility)
  | compare (cmp : UtilityComparator) (uf : UtilityFn) (φ₁ φ₂ : Formula World)

abbrev UtilitarianTheory (World : Type u) (Utility : Type u) (UtilityFn : Type u) : Type (max u 1) :=
  Theory (UtilitarianSentence World Utility UtilityFn)

/--
Minimal virtue-ethics sentence forms.

These are deliberately “schema-like” sentences (they talk about all agents with a virtue),
because that’s where inter-paradigm translations tend to live.
-/
inductive VirtueEthicsSentence (World : Type u) (Agent : Type u) (Virtue : Type u) : Type (max u 1)
  | hasVirtue (a : Agent) (v : Virtue)
  | virtueDesire (v : Virtue) (φ : Formula World)
  | virtuePref (v : Virtue) (φ₁ φ₂ : Formula World)

abbrev VirtueEthicsTheory (World : Type u) (Agent : Type u) (Virtue : Type u) : Type (max u 1) :=
  Theory (VirtueEthicsSentence World Agent Virtue)

/--
A single “mixed” ethical language, useful for meta-theory statements that quantify over
paradigms or talk about translations between them.
-/
inductive EthicalSentence (World : Type u) (Utility : Type u) (UtilityFn : Type u) (Agent : Type u) (Virtue : Type u) :
    Type (max u 1)
  | deontic (s : DeonticSentence World)
  | value (s : ValueJudgmentSentence World)
  | util (s : UtilitarianSentence World Utility UtilityFn)
  | virtue (s : VirtueEthicsSentence World Agent Virtue)

abbrev EthicalTheory (World : Type u) (Utility : Type u) (UtilityFn : Type u) (Agent : Type u) (Virtue : Type u) :
    Type (max u 1) :=
  Theory (EthicalSentence World Utility UtilityFn Agent Virtue)

/-- The simple definitional bridge: deontic theories can be pushed into value-judgment theories. -/
def DeontologicalImperativeTheory.toValueJudgmentTheory {World : Type u} (T : DeontologicalImperativeTheory World) :
    ValueJudgmentTheory World :=
  Theory.map DeonticSentence.toValue T

def ValueJudgmentTheory.toDeontologicalImperativeTheory {World : Type u} (T : ValueJudgmentTheory World) :
    DeontologicalImperativeTheory World :=
  Theory.map ValueJudgmentSentence.toDeontic T

/--
If the deontic and value semantics are aligned on tag translation, then models of a deontic
theory are exactly the models of its translated value-judgment theory.
-/
theorem models_deontic_iff_models_value {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (w : World) (T : DeontologicalImperativeTheory World) :
    Models (deonticSemantics World semD) w T ↔
      Models (valueJudgmentSemantics World semV) w (T.toValueJudgmentTheory) := by
  simpa [DeontologicalImperativeTheory.toValueJudgmentTheory] using
    (models_map_iff
      (sem₁ := deonticSemantics World semD)
      (sem₂ := valueJudgmentSemantics World semV)
      (f := DeonticSentence.toValue)
      (h_sat := fun w s => DeonticSemantics.sat_iff_sat_toValue (semD := semD) (semV := semV) h_align w s)
      (m := w) (T := T))

/-- Entailment preservation/equivalence for the deontic → value-judgment translation. -/
theorem entails_deontic_iff_entails_value {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (T : DeontologicalImperativeTheory World) (s : DeonticSentence World) :
    Entails (deonticSemantics World semD) T s ↔
      Entails (valueJudgmentSemantics World semV) (T.toValueJudgmentTheory) s.toValue := by
  simpa [DeontologicalImperativeTheory.toValueJudgmentTheory] using
    (entails_map_iff
      (sem₁ := deonticSemantics World semD)
      (sem₂ := valueJudgmentSemantics World semV)
      (f := DeonticSentence.toValue)
      (h_sat := fun w s => DeonticSemantics.sat_iff_sat_toValue (semD := semD) (semV := semV) h_align w s)
      (T := T) (s := s))

end Foet
