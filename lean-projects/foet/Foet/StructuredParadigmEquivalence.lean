import Foet.ParadigmEquivalence
import Foet.StructuredParadigms

set_option autoImplicit false

namespace Foet

universe u

/-!
Structured “paradigm loop”:

The ESOWIKI loop is stated for *sentences*, but the real goal is that it scales
to arbitrary structured sentences (with connectives/quantifiers) by recursion.

Here we lift the existing atomic `ValueJudgmentSentence.paradigmLoop` to
`StructuredSentence` by mapping it at leaves and leaving non-modal formulas alone.
-/

def structuredValueAtomLoop {World : Type u} : StructuredValueAtom World → StructuredValueAtom World
  | .inl s => .inl s.paradigmLoop
  | .inr φ => .inr φ

def structuredParadigmLoop {World : Type u} :
    StructuredSentence World (StructuredValueAtom World) → StructuredSentence World (StructuredValueAtom World) :=
  StructuredSentence.map structuredValueAtomLoop

theorem structuredValueAtomLoop_id {World : Type u} (a : StructuredValueAtom World) :
    structuredValueAtomLoop (World := World) a = a := by
  cases a with
  | inl s =>
      simpa [structuredValueAtomLoop] using
        congrArg (fun t => (Sum.inl (β := Formula World) t))
          (ValueJudgmentSentence.paradigmLoop_id (World := World) s)
  | inr φ =>
      rfl

theorem structuredParadigmLoop_id {World : Type u} (s : StructuredSentence World (StructuredValueAtom World)) :
    structuredParadigmLoop (World := World) s = s := by
  induction s with
  | atom a =>
      simp [structuredParadigmLoop, StructuredSentence.map, structuredValueAtomLoop_id (World := World)]
  | and p q ihp ihq =>
      have ihp' : StructuredSentence.map structuredValueAtomLoop p = p := by
        simpa [structuredParadigmLoop] using ihp
      have ihq' : StructuredSentence.map structuredValueAtomLoop q = q := by
        simpa [structuredParadigmLoop] using ihq
      dsimp [structuredParadigmLoop, StructuredSentence.map]
      rw [ihp', ihq']
  | or p q ihp ihq =>
      have ihp' : StructuredSentence.map structuredValueAtomLoop p = p := by
        simpa [structuredParadigmLoop] using ihp
      have ihq' : StructuredSentence.map structuredValueAtomLoop q = q := by
        simpa [structuredParadigmLoop] using ihq
      dsimp [structuredParadigmLoop, StructuredSentence.map]
      rw [ihp', ihq']
  | not p ih =>
      have ih' : StructuredSentence.map structuredValueAtomLoop p = p := by
        simpa [structuredParadigmLoop] using ih
      dsimp [structuredParadigmLoop, StructuredSentence.map]
      rw [ih']
  | imp p q ihp ihq =>
      have ihp' : StructuredSentence.map structuredValueAtomLoop p = p := by
        simpa [structuredParadigmLoop] using ihp
      have ihq' : StructuredSentence.map structuredValueAtomLoop q = q := by
        simpa [structuredParadigmLoop] using ihq
      dsimp [structuredParadigmLoop, StructuredSentence.map]
      rw [ihp', ihq']
  | iff p q ihp ihq =>
      have ihp' : StructuredSentence.map structuredValueAtomLoop p = p := by
        simpa [structuredParadigmLoop] using ihp
      have ihq' : StructuredSentence.map structuredValueAtomLoop q = q := by
        simpa [structuredParadigmLoop] using ihq
      dsimp [structuredParadigmLoop, StructuredSentence.map]
      rw [ihp', ihq']
  | forall_ g ih =>
      dsimp [structuredParadigmLoop, StructuredSentence.map]
      apply congrArg StructuredSentence.forall_
      funext x
      exact ih x
  | exists_ g ih =>
      dsimp [structuredParadigmLoop, StructuredSentence.map]
      apply congrArg StructuredSentence.exists_
      funext x
      exact ih x

end Foet
