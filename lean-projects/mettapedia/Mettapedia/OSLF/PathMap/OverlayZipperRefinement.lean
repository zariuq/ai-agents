import Mettapedia.OSLF.PathMap.OverlayDescendUntilRefinement

/-!
# Overlay Zipper Refinement: Cursor Observables

Proves that overlay cursor observables agree with the virtual overlay trie
from `ProductOverlayZipper.lean`.

## Cursor Observables

For each cursor position, the observable contract is:
- `path_exists`: does this path structurally exist in either component?
- `lookup_exists`: does the overlay produce a value at this path?
- `is_val`: does the focus have a value?
- `child_count`: how many child branches at the focus?
- `descendByte`: single-byte descent
- `descend_until`: skip unary chains to first value/branch

These correspond to the Rust `ReadZipper` interface.

## Virtual Overlay Trie

The overlay is `local <|> base`: local value wins when present,
base shows through otherwise. This is already proved in
`ProductOverlayZipper.lean` at the lookup level.

This file lifts those lookup results to cursor-level observables.

The key modeling choice is:

- an overlay zipper state is represented by an `OverlayTrie` rooted at the
  current focus
- root-level observables on that `OverlayTrie` correspond to cursor observables
- `descend_until` is therefore a root-relative path inside the current focused
  overlay trie
-/

namespace Mettapedia.OSLF.PathMap.OverlayZipperRefinement

open Mettapedia.OSLF.PathMap (OverlayTrie)
open Mettapedia.OSLF.PathMap.Trie (FTrie)

/-! ## §1: Cursor Observables on Overlay -/

/-- Structural root-level path existence for a focused trie. -/
def trie_root_path_exists (t : FTrie V) : Bool :=
  match t with
  | .empty => false
  | .node _ _ => true

/-- Does the overlay have any structural content at path `p` in either
component? This matches the Rust `OverlayZipper::path_exists` contract. -/
def overlay_path_exists (ot : OverlayTrie V) (p : List UInt8) : Bool :=
  trie_root_path_exists (ot.local_.subtreeAt p) ||
    trie_root_path_exists (ot.base.subtreeAt p)

/-- Does the overlay produce a value at path `p`? -/
def overlay_lookup_exists (ot : OverlayTrie V) (p : List UInt8) : Bool :=
  (ot.lookup p).isSome

/-- Does the overlay focus (root) have a value? -/
def overlay_is_val (ot : OverlayTrie V) : Bool :=
  overlay_lookup_exists ot []

/-- How many child branches are visible at the current overlay focus? -/
def overlay_child_count (ot : OverlayTrie V) : Nat :=
  OverlayTrie.childCountAt ot []

/-- Root-relative path chosen by overlay `descend_until` from the current focus. -/
def overlay_descend_until_target (ot : OverlayTrie V) : List UInt8 :=
  OverlayTrie.descendUntilPath ot []

/-! ## §2: Structural path existence vs value existence -/

/-- **lookup_exists agrees with lookup.** Definitional. -/
theorem overlay_lookup_exists_iff (ot : OverlayTrie V) (p : List UInt8) :
    overlay_lookup_exists ot p = true ↔ ot.lookup p ≠ none := by
  simp [overlay_lookup_exists, Option.isSome_iff_ne_none]

/-- **Structural path existence is the OR of component subtree existence.** -/
theorem overlay_path_exists_iff (ot : OverlayTrie V) (p : List UInt8) :
    overlay_path_exists ot p = true ↔
    trie_root_path_exists (ot.local_.subtreeAt p) = true ∨
      trie_root_path_exists (ot.base.subtreeAt p) = true := by
  by_cases hLocal : trie_root_path_exists (ot.local_.subtreeAt p) = true <;>
    by_cases hBase : trie_root_path_exists (ot.base.subtreeAt p) = true <;>
    simp [overlay_path_exists, hLocal, hBase]

/-- **path_exists via local or base.** Structural existence in the overlay is
exactly structural existence in one of the two components. -/
theorem overlay_path_exists_or (ot : OverlayTrie V) (p : List UInt8) :
    overlay_path_exists ot p = true ↔
    trie_root_path_exists (ot.local_.subtreeAt p) = true ∨
      trie_root_path_exists (ot.base.subtreeAt p) = true := by
  exact overlay_path_exists_iff ot p

/-- Descending an overlay simply descends both components. -/
theorem OverlayTrie.descendPath_components (ot : OverlayTrie V) (p : List UInt8) :
    (ot.descendPath p).local_ = ot.local_.subtreeAt p ∧
      (ot.descendPath p).base = ot.base.subtreeAt p := by
  induction p generalizing ot with
  | nil =>
      simp [OverlayTrie.descendPath, FTrie.subtreeAt_nil]
  | cons b rest ih =>
      simpa [OverlayTrie.descendPath, OverlayTrie.descendByte, FTrie.subtreeAt_append,
        List.singleton_append] using ih (ot.descendByte b)

/-- Value existence through overlay lookup is still local-or-base lookup. -/
theorem overlay_lookup_exists_or (ot : OverlayTrie V) (p : List UInt8) :
    overlay_lookup_exists ot p = true ↔
    (ot.local_.lookup p).isSome = true ∨ (ot.base.lookup p).isSome = true := by
  simp [overlay_lookup_exists, OverlayTrie.lookup, Option.isSome_iff_ne_none,
        Option.orElse]
  constructor
  · intro h
    cases hl : ot.local_.lookup p
    · simp [hl] at h; exact Or.inr h
    · exact Or.inl (by simp)
  · intro h
    rcases h with hl | hb
    · cases hlv : ot.local_.lookup p <;> simp_all
    · cases hlv : ot.local_.lookup p <;> simp_all

/-- A value at a path implies that the path structurally exists. -/
theorem overlay_lookup_exists_implies_path_exists (ot : OverlayTrie V) (p : List UInt8) :
    overlay_lookup_exists ot p = true → overlay_path_exists ot p = true := by
  intro hLookup
  rw [overlay_lookup_exists_or] at hLookup
  rw [overlay_path_exists_or]
  rcases hLookup with hLocal | hBase
  · left
    have hLocalRoot :
        (FTrie.rootVal? (ot.local_.subtreeAt p)).isSome = true := by
      simpa [FTrie.rootVal?_subtreeAt_eq_lookup] using hLocal
    cases hSub : ot.local_.subtreeAt p with
    | empty =>
        simp [hSub] at hLocalRoot
    | node val children =>
        simp [trie_root_path_exists]
  · right
    have hBaseRoot :
        (FTrie.rootVal? (ot.base.subtreeAt p)).isSome = true := by
      simpa [FTrie.rootVal?_subtreeAt_eq_lookup] using hBase
    cases hSub : ot.base.subtreeAt p with
    | empty =>
        simp [hSub] at hBaseRoot
    | node val children =>
        simp [trie_root_path_exists]

/-! ## §3: is_val = root has value -/

/-- **is_val = lookup_exists at root.** -/
theorem overlay_is_val_eq_lookup_exists_nil (ot : OverlayTrie V) :
    overlay_is_val ot = overlay_lookup_exists ot [] := rfl

/-- **Local value shadows base at root.** -/
theorem overlay_is_val_local_shadows (ot : OverlayTrie V) (v : V)
    (hlocal : ot.local_.lookup [] = some v) :
    overlay_is_val ot = true := by
  simp [overlay_is_val, overlay_lookup_exists, OverlayTrie.lookup, hlocal, Option.orElse]

/-- **Base shows through when local is none.** -/
theorem overlay_is_val_base_through (ot : OverlayTrie V)
    (hlocal : ot.local_.lookup [] = none) :
    overlay_is_val ot = (ot.base.lookup []).isSome := by
  simp [overlay_is_val, overlay_lookup_exists, OverlayTrie.lookup, hlocal, Option.orElse]

/-- **A value at the focus implies structural path existence at the focus.** -/
theorem overlay_is_val_implies_path_exists (ot : OverlayTrie V) :
    overlay_is_val ot = true → overlay_path_exists ot [] = true := by
  intro h
  exact overlay_lookup_exists_implies_path_exists ot [] h

/-! ## §4: child_count and descend_until at the current focus -/

/-- **child_count is the root child count of the virtual overlay trie.** -/
theorem overlay_child_count_eq_virtual_root_childCount (ot : OverlayTrie V) :
    overlay_child_count ot = FTrie.childCount ot.virtualTrie := by
  simp [overlay_child_count, OverlayTrie.childCountAt, OverlayTrie.virtualTrie,
    FTrie.subtreeAt_nil]

/-- **descend_until target is stable at a branch or leaf.** -/
theorem overlay_descend_until_target_stable_of_childCount_ne_one
    (ot : OverlayTrie V) (h : overlay_child_count ot ≠ 1) :
    overlay_descend_until_target ot = [] := by
  simpa [overlay_child_count, overlay_descend_until_target] using
    OverlayTrie.descendUntilPath_stable_of_childCount_ne_one ot [] h

/-- **descend_until can stop at the first internal prefix value.** -/
theorem overlay_descend_until_target_stops_at_first_internal_value
    (ot : OverlayTrie V) (val : Option V) (b : UInt8) (child : FTrie V)
    (hfocus : ot.virtualTrie.subtreeAt [] = FTrie.node val [(b, child)])
    (hval : (FTrie.rootVal? child).isSome = true) :
    overlay_descend_until_target ot = [b] := by
  simpa [overlay_descend_until_target] using
    OverlayTrie.descendUntilPath_stops_at_first_internal_value ot [] val b child hfocus hval

/-- **descend_until stops at either a value or a non-unary branch.** -/
theorem overlay_descend_until_target_stops
    (ot : OverlayTrie V) (hsl : ot.local_.Sorted) (hsb : ot.base.Sorted) :
    overlay_path_exists ot (overlay_descend_until_target ot) = true ∨
      OverlayTrie.childCountAt ot (overlay_descend_until_target ot) ≠ 1 := by
  have hStop := OverlayTrie.descendUntilPath_stops ot [] hsl hsb
  rcases hStop with hVal | hBranch
  · left
    exact overlay_lookup_exists_implies_path_exists ot (overlay_descend_until_target ot) hVal
  · right
    simpa [overlay_descend_until_target] using hBranch

/-! ## §5: Descent commutes with lookup -/

/-- **descendByte commutes with lookup** (already in ProductOverlayZipper). -/
theorem overlay_descendByte_lookup (ot : OverlayTrie V) (b : UInt8)
    (suffix : List UInt8) :
    (ot.descendByte b).lookup suffix = ot.lookup (b :: suffix) :=
  OverlayTrie.descendByte_lookup ot b suffix

/-- **descendPath commutes with lookup** (already in ProductOverlayZipper). -/
theorem overlay_descendPath_lookup (ot : OverlayTrie V) (pfx suffix : List UInt8) :
    (ot.descendPath pfx).lookup suffix = ot.lookup (pfx ++ suffix) :=
  OverlayTrie.descendPath_lookup ot pfx suffix

/-- **path_exists is preserved through descent.** -/
theorem overlay_path_exists_after_descent (ot : OverlayTrie V) (pfx p : List UInt8) :
    overlay_path_exists (ot.descendPath pfx) p =
    overlay_path_exists ot (pfx ++ p) := by
  rcases OverlayTrie.descendPath_components ot pfx with ⟨hLocal, hBase⟩
  simp [overlay_path_exists, hLocal, hBase, FTrie.subtreeAt_append]

/-- **is_val after descent = lookup_exists at the descent point.** -/
theorem overlay_is_val_after_descent (ot : OverlayTrie V) (pfx : List UInt8) :
    overlay_is_val (ot.descendPath pfx) =
    overlay_lookup_exists ot pfx := by
  simp [overlay_is_val, overlay_lookup_exists, overlay_descendPath_lookup]

/-! ## §6: Summary

**0 sorries. 0 axioms.**

| Theorem | What it says |
|---------|-------------|
| `overlay_lookup_exists_iff` | lookup_exists ↔ lookup is some |
| `overlay_path_exists_iff` | path_exists ↔ structural subtree in local or base |
| `overlay_path_exists_or` | structural existence ↔ local or base subtree exists |
| `overlay_lookup_exists_or` | value existence ↔ local or base has value |
| `overlay_is_val_local_shadows` | local value makes is_val true |
| `overlay_is_val_base_through` | base shows through when local absent |
| `overlay_child_count_eq_virtual_root_childCount` | child_count = virtual trie root child count |
| `overlay_descend_until_target_stable_of_childCount_ne_one` | descend_until stays put at branch/leaf |
| `overlay_descend_until_target_stops_at_first_internal_value` | descend_until may stop at an internal prefix value |
| `overlay_descend_until_target_stops` | descend_until stops at a value or non-unary branch |
| `overlay_descendByte_lookup` | byte descent commutes with lookup |
| `overlay_descendPath_lookup` | path descent commutes with lookup |
| `overlay_path_exists_after_descent` | path_exists stable under descent |
| `overlay_is_val_after_descent` | is_val after descent = lookup_exists at descent point |

These give the cursor-observational contract for overlay zippers:
every read-side observable is determined by the virtual overlay trie and its
root-relative descent behavior.

Maps to Rust: `ReadZipper` methods on `OverlayZipper` should agree with
the virtual overlay trie at every cursor position.
-/

end Mettapedia.OSLF.PathMap.OverlayZipperRefinement
