import Mettapedia.OSLF.PathMap.Trie.CoinductiveTrie
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement
import Mettapedia.OSLF.PathMap.Core

/-!
# Trie PathMap Instance

`FTrie V` satisfies `PathMapQuantale` when `V` has lawful `BEq`.
Operations use identity detection (BEq) for structural-sharing optimization.

## Notes on Commutativity

FTrie.join is LEFT-BIASED: when both tries have values at the same path,
the left value is kept (`v₁ <|> v₂ = v₁`).  This means `JoinComm` does
NOT hold for general `V` with multiple distinct values.

For the PathMap use case (set of paths, `V = Unit`), commutativity holds
trivially since `Unit` has a single value.

## References

- Core.lean: `PathMapQuantale`, `AlgebraicResult`
- FiniteTrie.lean: `FTrie` operations
- TrieRefinement.lean: lookup correctness theorems
-/

open Mettapedia.PathMap

namespace Mettapedia.OSLF.PathMap.Trie

namespace FTrie

universe u

variable {V : Type u}

/-! ## §1: BEq Infrastructure -/

mutual
  /-- Structural equality for FTrie. -/
  def beqFTrie [BEq V] : FTrie V → FTrie V → Bool
    | .empty, .empty => true
    | .node v₁ c₁, .node v₂ c₂ => v₁ == v₂ && beqChildren c₁ c₂
    | _, _ => false

  /-- Structural equality for child lists. -/
  def beqChildren [BEq V] : List (UInt8 × FTrie V) → List (UInt8 × FTrie V) → Bool
    | [], [] => true
    | (k₁, t₁) :: r₁, (k₂, t₂) :: r₂ => k₁ == k₂ && beqFTrie t₁ t₂ && beqChildren r₁ r₂
    | _, _ => false
end

instance [BEq V] : BEq (FTrie V) := ⟨beqFTrie⟩

mutual
  theorem beqFTrie_refl [BEq V] [LawfulBEq V] (a : FTrie V) : beqFTrie a a = true := by
    cases a with
    | empty => unfold beqFTrie; rfl
    | node v cs => unfold beqFTrie; simp [beqChildren_refl cs]

  theorem beqChildren_refl [BEq V] [LawfulBEq V] (cs : List (UInt8 × FTrie V)) :
      beqChildren cs cs = true := by
    match cs with
    | [] => unfold beqChildren; rfl
    | (k, t) :: rest =>
      unfold beqChildren; simp [beqFTrie_refl t, beqChildren_refl rest]
end

/-! ## §2: PathMapQuantale Instance -/

instance [BEq V] [LawfulBEq V] : PathMapQuantale (FTrie V) where
  pjoin a b :=
    match a, b with
    | .empty, .empty => .none
    | .empty, _ => .identity false true
    | _, .empty => .identity true false
    | _, _ => if beqFTrie a b then .identity true true else .element (a.join b)
  pmeet a b :=
    match a, b with
    | .empty, _ | _, .empty => .none
    | _, _ =>
      if beqFTrie a b then .identity true true
      else let r := a.meet b
           if beqFTrie r .empty then .none else .element r
  psubtract a b :=
    match a, b with
    | .empty, _ => .none
    | _, .empty => .identity true false
    | _, _ =>
      if beqFTrie a b then .none
      else let r := a.subtract b
           if beqFTrie r .empty then .none else .element r
  prestrict a b :=
    match a, b with
    | .empty, _ | _, .empty => .none
    | _, _ =>
      if beqFTrie a b then .identity true true
      else let r := a.restrict b
           if beqFTrie r .empty then .none else .element r

/-! ## §3: Algebraic Laws -/

instance [BEq V] [LawfulBEq V] : JoinIdem (FTrie V) where
  pjoin_idem a := by
    simp only [PathMapLattice.pjoin, AlgebraicResult.isElem]
    cases a with
    | empty => simp
    | node v cs => simp [beqFTrie_refl]

instance [BEq V] [LawfulBEq V] : MeetIdem (FTrie V) where
  pmeet_idem a := by
    simp only [PathMapLattice.pmeet, AlgebraicResult.isElem]
    cases a with
    | empty => simp
    | node v cs => simp [beqFTrie_refl]

/-! ## §4: Summary

`FTrie V` is a `PathMapQuantale` with identity detection via structural BEq.
Laws proven: `JoinIdem`, `MeetIdem`.

`JoinComm` and `MeetComm` hold for `V = Unit` (single-valued paths) but not
for general `V` due to the left-biased value merge (`v₁ <|> v₂`).
-/

end FTrie

end Mettapedia.OSLF.PathMap.Trie
