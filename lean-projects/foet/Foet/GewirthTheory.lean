import Foet.GewirthPGC

set_option autoImplicit false

namespace Foet

namespace Gewirth

universe u

namespace WorldSet

abbrev Union {World : Type u} (X Y : Formula World) : Formula World :=
  fun w => X w ∨ Y w

abbrev Compl {World : Type u} (X : Formula World) : Formula World :=
  fun w => ¬ X w

end WorldSet

/--
Package the non-logical symbols and semantic frames used by the AFP Gewirth PGC development.

This lets us treat the axioms as an explicit `Theory` (a set of sentences) in the FOET sense.
-/
abbrev PGCModel : Type (u + 1) :=
  PGCInterpretation

/--
The Gewirth PGC *assumption set* (all statements except the goal), as a FOET `Theory`.

This corresponds to the AFP session’s axiomatizations/premises; the goal (`PGC_strong`) is excluded.
-/
def PGCAssumptionTheory : Theory PGCStatementName :=
  fun s => s ≠ .PGC_strong

/--
Satisfaction relation for `PGCStatementName`s in a `PGCModel`.

Each axiom name is interpreted as the corresponding HOL proposition about the model.
-/
def pgcSemantics : Semantics PGCStatementName PGCModel :=
  ⟨fun m s =>
    PGCStatement m s⟩

/-- The AFP axiom set entails the (strong) PGC theorem, expressed as a sentence. -/
theorem entails_PGC_strong :
    Entails pgcSemantics PGCAssumptionTheory PGCStatementName.PGC_strong := by
  intro m hm
  have hAssm : Gewirth.PGCAssumptions m := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hm .sem_5a (by intro h; cases h)
    · exact hm .sem_5b (by intro h; cases h)
    · exact hm .sem_5e (by intro h; cases h)
    · exact hm .explicationGoodness1 (by intro h; cases h)
    · exact hm .explicationGoodness2 (by intro h; cases h)
    · exact hm .explicationGoodness3 (by intro h; cases h)
    · exact hm .explicationFWB1 (by intro h; cases h)
    · exact hm .explicationFWB2 (by intro h; cases h)
    · exact hm .explicationFWB3 (by intro h; cases h)
    · exact hm .OIOAC (by intro h; cases h)
    · exact hm .explicationInterference (by intro h; cases h)
  exact PGC_strong_ofAssumptions m hAssm

/--
Additional frame axioms from `CJDDLplus.thy` (the Carmo–Jones DDL embedding),
kept separate from `PGCAssumptionTheory` because the PGC proof does not require them.
-/
inductive PGCAFPExtraSentence : Type
  | sem_3a
  | sem_4a
  | sem_4b
  | sem_5c
  | sem_5d
  deriving DecidableEq, Repr

/-- A “full AFP-aligned” sentence type: minimal PGC sentences + the extra DDL frame axioms. -/
inductive PGCAFPSentence : Type
  | base (s : PGCStatementName)
  | extra (s : PGCAFPExtraSentence)
  deriving DecidableEq, Repr

def PGCAFPTheory : Theory PGCAFPSentence :=
  fun s => s ≠ .base .PGC_strong

def pgcAfpSemantics : Semantics PGCAFPSentence PGCModel :=
  ⟨fun m s =>
    match s with
    | .base sBase =>
        pgcSemantics.Sat m sBase
    | .extra .sem_3a =>
        ∀ w : m.World, Instantiated (m.av w)
    | .extra .sem_4a =>
        ∀ w : m.World, Subset (m.av w) (m.pv w)
    | .extra .sem_4b =>
        ∀ w : m.World, m.pv w w
    | .extra .sem_5c =>
        ∀ X Y Z : Formula m.World,
          (Instantiated (Inter (Inter X Y) Z) ∧ m.ob X Y ∧ m.ob X Z) →
            m.ob X (Inter Y Z)
    | .extra .sem_5d =>
        ∀ X Y Z : Formula m.World,
          (Subset Y X ∧ m.ob X Y ∧ Subset X Z) →
            m.ob Z (WorldSet.Union (Inter Z (WorldSet.Compl X)) Y)⟩

/--
Full AFP-aligned route: if a model satisfies the CJDDLplus frame axioms in addition to the
Gewirth explications, then it satisfies `PGC_strong`.

This makes the “extra axioms are not needed” claim explicit: the proof works under a weaker
assumption set, hence also under the stronger AFP one.
-/
theorem entails_PGC_strong_from_AFPTheory :
    Entails pgcAfpSemantics PGCAFPTheory (.base .PGC_strong) := by
  intro m hm
  have hmBase : Models pgcSemantics m PGCAssumptionTheory := by
    intro s hs
    have : PGCAFPSentence.base s ∈ PGCAFPTheory := by
      intro hEq
      -- `hs : s ≠ .PGC_strong`
      exact hs (by cases hEq; rfl)
    exact hm (.base s) this
  exact entails_PGC_strong m hmBase

end Gewirth

end Foet
