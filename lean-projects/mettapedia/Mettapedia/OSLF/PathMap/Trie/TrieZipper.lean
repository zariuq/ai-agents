import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.ZipperExecution

/-!
# Trie Zipper — ZipperIterationSound for FTrie

A `SimpleTrieZipper V` wraps an `FTrie V` with its entries list,
providing a cursor that iterates over all stored values in DFS order.

The zipper satisfies `ZipperIterationSound`: the set of values reachable
by `toNextVal` iteration equals the set of stored values.

## Design

We use a simplified zipper that flattens the trie structure into an entries
list.  Navigation is degenerate (always at root/leaf, no children), and
iteration advances through the entries list.  This matches the `FlatZipper`
pattern and proves the same soundness contract.

A full Huet-style trie zipper (with stack frames and structural navigation)
can be built as a refinement; the soundness proof transfers via the entries
characterization.

## References

- FlatZipperInstance.lean: reference implementation pattern
- ZipperExecution.lean: `ZipperIterationSound` spec
- FiniteTrie.lean: `FTrie.entries`
-/

open Mettapedia.PathMap
open Mettapedia.OSLF.PathMap.ZipperExecution

namespace Mettapedia.OSLF.PathMap.Trie

universe u

variable {V : Type u}

/-! ## §1: Core Type -/

/-- A simplified trie zipper: wraps an FTrie with its remaining entries. -/
structure SimpleTrieZipper (V : Type u) where
  /-- The underlying trie (for reconstruction). -/
  trie : FTrie V
  /-- Remaining entries to visit (path, value) pairs in DFS order. -/
  remaining : List (List UInt8 × V)

/-- Create a zipper from an FTrie, initialized to iterate all entries. -/
def SimpleTrieZipper.fromTrie (t : FTrie V) : SimpleTrieZipper V :=
  ⟨t, t.entries⟩

/-! ## §2: Typeclass Instances -/

instance : ZipperMoving (SimpleTrieZipper V) where
  descendFirstByte _ := none
  descendLastByte  _ := none
  ascend           _ := none
  currentPath      _ := []
  atLeaf           _ := true
  atRoot           _ := true

instance : ZipperBounded (SimpleTrieZipper V) where
  ascend_none_at_root _ _ := rfl

instance : ZipperValues (SimpleTrieZipper V) V where
  valueAt z := z.remaining.head?.map Prod.snd

instance : ZipperIteration (SimpleTrieZipper V) where
  toNextVal z := match z.remaining with
    | []          => (⟨z.trie, []⟩, false)
    | [_]         => (⟨z.trie, []⟩, false)
    | _ :: rest   => (⟨z.trie, rest⟩, true)
  descendLastPath z   := (z, false)
  descendFirstKPath z
    | 0     => (z, true)
    | _ + 1 => (z, false)
  toNextKPath z _ := (z, false)

instance : ZipperStoreValues (SimpleTrieZipper V) V where
  allValues z := z.remaining.map Prod.snd

/-! ## §3: Soundness Proof -/

/-- Every value reachable from a SimpleTrieZipper is in its remaining entries. -/
private theorem reachable_subset (z : SimpleTrieZipper V) (v : V)
    (h : ZipperReachableValue z v) : v ∈ (z.remaining.map Prod.snd) := by
  induction h with
  | here z v hv =>
    simp only [ZipperValues.valueAt] at hv
    match hz : z.remaining with
    | [] => simp [hz] at hv
    | (p, w) :: rest =>
      simp [hz] at hv; subst hv; simp
  | step z v hnext _ ih =>
    match hz : z.remaining with
    | [] => simp [hz, ZipperIteration.toNextVal] at hnext
    | [_] => simp [hz, ZipperIteration.toNextVal] at hnext
    | _ :: _ :: _ =>
      simp only [hz, ZipperIteration.toNextVal] at ih
      exact List.mem_cons_of_mem _ ih

/-- Every value in a SimpleTrieZipper's entries is reachable by iteration. -/
private theorem elem_reachable (remaining : List (List UInt8 × V)) (t : FTrie V)
    (v : V) (h : v ∈ remaining.map Prod.snd) :
    ZipperReachableValue (SimpleTrieZipper.mk t remaining) v := by
  induction remaining with
  | nil => simp at h
  | cons hd rest ih =>
    simp only [List.map, List.mem_cons] at h
    rcases h with rfl | hmem
    · exact .here _ _ (by simp [ZipperValues.valueAt])
    · match hrest : rest with
      | [] => simp at hmem
      | b :: tl =>
        apply ZipperReachableValue.step _ _ rfl
        simp only [ZipperIteration.toNextVal]
        exact ih hmem

/-- The SimpleTrieZipper is iteration-sound: reachable values = stored values. -/
instance : ZipperIterationSound (SimpleTrieZipper V) V where
  reachable_in_store root v _ hreach := reachable_subset root v hreach
  store_in_reachable root v _ hmem := elem_reachable root.remaining root.trie v hmem

/-! ## §4: Additional Laws -/

instance : ZipperIterationRooted (SimpleTrieZipper V) where
  toNextVal_false_at_root _ _ _ _ := rfl

instance : ZipperIterationZeroDepth (SimpleTrieZipper V) where
  descendFirstKPath_zero _ := ⟨rfl, rfl⟩

instance : ZipperComplexity (SimpleTrieZipper V) where
  descendFirstKPath_depth_le _ k hk := by
    match k with
    | 0 => simp [ZipperMoving.currentPath]
    | _ + 1 => simp [ZipperIteration.descendFirstKPath] at hk
  toNextVal_depth_bounded _ _ := by
    simp [ZipperMoving.currentPath]

/-! ## §5: Summary

`SimpleTrieZipper V` is a proven `ZipperIterationSound` implementation
backed by `FTrie.entries`.  Additional laws: `ZipperIterationRooted`,
`ZipperIterationZeroDepth`, `ZipperComplexity`.
-/

end Mettapedia.OSLF.PathMap.Trie
