import Mettapedia.OSLF.PathMap.Trie.DescendUntilRefinement

/-!
# Product Zipper Refinement: Root-Level Observables

This file formalizes the read-side observable contract for product zippers at
the current focus.

The key Rust seam in `product_zipper.rs` is that a factor boundary can expose:

- `path_exists` / `is_val` from the completed factor
- `child_count` from the next factor root

So the right mathematical object is not a plain trie focus, but a **stitched
cursor state** carrying:

- an optional completed-factor focus that still determines whether the current
  absolute path exists and has a value
- an active factor focus that determines visible children and byte descent
- the remaining factors

This file keeps that seam explicit and proves the core `descend_until`
behavior needed to guide Rust:

- no movement at a branch or leaf
- seamless movement across factor boundaries
- stopping at the first internal value when present
-/

namespace Mettapedia.OSLF.PathMap

open Trie
open Trie.FTrie

/-- Root-level existence of the current focus. -/
def rootPathExists (t : FTrie Unit) : Bool :=
  match t with
  | .empty => false
  | .node _ _ => true

/-- Root-level value flag of the current focus. -/
def rootIsVal (t : FTrie Unit) : Bool :=
  (FTrie.rootVal? t).isSome

/-- Root-level cursor model for a product zipper over support tries.

`completed?` is the just-finished factor focus still visible at the current
absolute path. `active` is the factor currently supplying children. -/
structure ProductCursor where
  completed? : Option (FTrie Unit)
  active : FTrie Unit
  rest : List (FTrie Unit)

namespace ProductCursor

/-- Build a root cursor from a nonempty factor list. -/
def ofFactors : FTrie Unit → List (FTrie Unit) → ProductCursor
  | primary, rest => ⟨none, primary, rest⟩

/-- Is the current active factor focus a stitch point into the next factor? -/
def atFactorEnd (pc : ProductCursor) : Bool :=
  FTrie.childCount pc.active = 0 && rootPathExists pc.active = true

/-- Enter the next factor once, preserving the completed factor as the visible
value/path-existence source at this absolute path. -/
def stitch (pc : ProductCursor) : ProductCursor :=
  match pc.completed?, pc.rest with
  | some completed, _ => ⟨some completed, pc.active, pc.rest⟩
  | none, next :: rest =>
      if pc.atFactorEnd then
        ⟨some pc.active, next, rest⟩
      else
        pc
  | none, [] => pc

/-- Current absolute-path existence observable. -/
def pathExists (pc : ProductCursor) : Bool :=
  match pc.completed? with
  | some finished => rootPathExists finished
  | none => rootPathExists pc.active

/-- Current absolute-path value observable. -/
def isVal (pc : ProductCursor) : Bool :=
  match pc.completed? with
  | some finished => rootIsVal finished
  | none => rootIsVal pc.active

/-- Current child-count observable. Children always come from the active factor. -/
def childCount (pc : ProductCursor) : Nat :=
  FTrie.childCount pc.active

/-- Descend one byte inside the active factor, then stitch if a factor just ended. -/
def descendByte (pc : ProductCursor) (b : UInt8) : ProductCursor :=
  let child := pc.active.subtreeAt [b]
  stitch ⟨none, child, pc.rest⟩

/-- Termination measure for product descend-until: active factor plus remaining
factor mass. Completed-factor visibility does not contribute to future motion. -/
noncomputable def totalMass (pc : ProductCursor) : Nat :=
  sizeOf pc.active + pc.rest.foldr (fun t n => sizeOf t + n) 0

/-- Fuel-bounded root-relative descend-until suffix. -/
def descendUntilSuffixFuel : Nat → ProductCursor → List UInt8
  | 0, _ => []
  | fuel + 1, pc =>
      match pc.childCount, pc.active with
      | 1, .node _ [(b, _child)] =>
          let nextPc := pc.descendByte b
          if nextPc.isVal then
            [b]
          else
            b :: descendUntilSuffixFuel fuel nextPc
      | _, _ => []

/-- Root-relative descend-until suffix chosen by the product cursor. -/
noncomputable def descendUntilSuffix (pc : ProductCursor) : List UInt8 :=
  descendUntilSuffixFuel pc.totalMass pc

/-! ## §1: Observable contract at the current focus -/

/-- With a completed factor, path existence comes from the completed factor focus. -/
theorem pathExists_of_completed (finished next : FTrie Unit) (rest : List (FTrie Unit)) :
    (⟨some finished, next, rest⟩ : ProductCursor).pathExists = rootPathExists finished := by
  simp [pathExists]

/-- Without a completed factor, path existence comes from the active factor focus. -/
theorem pathExists_of_active (active : FTrie Unit) (rest : List (FTrie Unit)) :
    (⟨none, active, rest⟩ : ProductCursor).pathExists = rootPathExists active := by
  simp [pathExists]

/-- With a completed factor, root value visibility comes from the completed factor focus. -/
theorem isVal_of_completed (finished next : FTrie Unit) (rest : List (FTrie Unit)) :
    (⟨some finished, next, rest⟩ : ProductCursor).isVal = rootIsVal finished := by
  simp [isVal]

/-- Without a completed factor, root value visibility comes from the active factor focus. -/
theorem isVal_of_active (active : FTrie Unit) (rest : List (FTrie Unit)) :
    (⟨none, active, rest⟩ : ProductCursor).isVal = rootIsVal active := by
  simp [isVal]

/-- Child supply always comes from the active factor focus. -/
theorem childCount_eq_active (pc : ProductCursor) :
    pc.childCount = FTrie.childCount pc.active := rfl

/-- The current focus stays put when the visible children are not unary. -/
theorem descendUntilSuffixFuel_eq_nil_of_childCount_ne_one
    (fuel : Nat) (pc : ProductCursor) (h : pc.childCount ≠ 1) :
    descendUntilSuffixFuel fuel pc = [] := by
  cases fuel with
  | zero =>
      rfl
  | succ fuel =>
      cases pc with
      | mk completed? active rest =>
          cases active with
          | empty =>
              simp [descendUntilSuffixFuel, childCount] at h ⊢
          | node val children =>
              cases children with
              | nil =>
                  simp [descendUntilSuffixFuel, childCount] at h ⊢
              | cons hd tl =>
                  cases tl with
                  | nil =>
                      simp [childCount] at h
                  | cons hd2 tl2 =>
                      simp [descendUntilSuffixFuel, childCount]

/-- The current focus stays put when the visible children are not unary. -/
theorem descendUntilSuffix_eq_nil_of_childCount_ne_one (pc : ProductCursor)
    (h : pc.childCount ≠ 1) :
    pc.descendUntilSuffix = [] := by
  unfold descendUntilSuffix
  exact descendUntilSuffixFuel_eq_nil_of_childCount_ne_one pc.totalMass pc h

/-- A stitched cursor exposes path existence and value from the completed factor,
while children come from the next factor root. -/
theorem stitch_observables (finished next : FTrie Unit) (rest : List (FTrie Unit)) :
    let pc : ProductCursor := ⟨some finished, next, rest⟩
    pc.pathExists = rootPathExists finished ∧
    pc.isVal = rootIsVal finished ∧
    pc.childCount = FTrie.childCount next := by
  simp [pathExists, isVal, childCount]

/-! ## §2: One-byte descent and stitched-boundary observables -/

/-- Descending one byte preserves the reached child's path existence visibility,
even if stitching immediately enters the next factor. -/
theorem descendByte_pathExists_eq_rootPathExists_subtree
    (completed? : Option (FTrie Unit)) (active : FTrie Unit)
    (b : UInt8) (rest : List (FTrie Unit)) :
    (descendByte ⟨completed?, active, rest⟩ b).pathExists =
      rootPathExists (active.subtreeAt [b]) := by
  cases rest with
  | nil =>
      simp [descendByte, stitch, pathExists, rootPathExists]
  | cons next rest =>
      by_cases h :
          (ProductCursor.atFactorEnd
            { completed? := none
              active := active.subtreeAt [b]
              rest := next :: rest }) = true
      · simp [descendByte, stitch, pathExists, rootPathExists, h]
      · simp [descendByte, stitch, pathExists, rootPathExists, h]

/-- Descending one byte preserves the reached child's root-value visibility,
even if stitching immediately enters the next factor. -/
theorem descendByte_isVal_eq_rootIsVal_subtree
    (completed? : Option (FTrie Unit)) (active : FTrie Unit)
    (b : UInt8) (rest : List (FTrie Unit)) :
    (descendByte ⟨completed?, active, rest⟩ b).isVal =
      rootIsVal (active.subtreeAt [b]) := by
  cases rest with
  | nil =>
      simp [descendByte, stitch, isVal, rootIsVal]
  | cons next rest =>
      by_cases h :
          (ProductCursor.atFactorEnd
            { completed? := none
              active := active.subtreeAt [b]
              rest := next :: rest }) = true
      · simp [descendByte, stitch, isVal, rootIsVal, h]
      · simp [descendByte, stitch, isVal, rootIsVal, h]

/-! ## §3: descend_until behavior at stitched boundaries -/

/-- Product `descend_until` can stop at the first internal value reached after
crossing a factor boundary. -/
theorem descendUntilSuffix_stops_at_first_internal_value_after_boundary
    (fuel : Nat)
    (finished next : FTrie Unit) (rest : List (FTrie Unit))
    (b : UInt8) (child : FTrie Unit)
    (hnext : next = FTrie.node none [(b, child)])
    (hchild : rootIsVal child = true) :
    descendUntilSuffixFuel (fuel + 1) ⟨some finished, next, rest⟩ = [b] := by
  subst hnext
  have hnextVal :
      (descendByte ⟨some finished, FTrie.node none [(b, child)], rest⟩ b).isVal = true := by
    have hsub :
        rootIsVal ((FTrie.node none [(b, child)]).subtreeAt [b]) = true := by
      simpa [rootIsVal, FTrie.subtreeAt, FTrie.subtreeAt_nil, hchild]
    exact
      (descendByte_isVal_eq_rootIsVal_subtree
        (completed? := some finished)
        (active := FTrie.node none [(b, child)])
        (b := b) (rest := rest)).trans hsub
  simp [descendUntilSuffixFuel, childCount]
  rw [hnextVal]
  simp

/-- Wrapper corollary for the first-internal-value stop after a stitched boundary. -/
theorem descendUntilSuffix_stops_at_first_internal_value_after_boundary_total
    (finished next : FTrie Unit) (rest : List (FTrie Unit))
    (b : UInt8) (child : FTrie Unit)
    (hnext : next = FTrie.node none [(b, child)])
    (hchild : rootIsVal child = true) :
    descendUntilSuffix ⟨some finished, next, rest⟩ = [b] := by
  unfold descendUntilSuffix
  have hMass :
      totalMass ⟨some finished, next, rest⟩ ≠ 0 := by
    simp [totalMass, hnext]
  cases hFuel : totalMass ⟨some finished, next, rest⟩ with
  | zero =>
      contradiction
  | succ fuel =>
      simpa [hFuel] using
        descendUntilSuffix_stops_at_first_internal_value_after_boundary
          fuel finished next rest b child hnext hchild

/-! ## Examples -/

def danglingSnip : FTrie Unit :=
  FTrie.node none [(45, FTrie.node none [(61, FTrie.node none [])])]

def stitchedDangling : ProductCursor :=
  ⟨some danglingSnip, danglingSnip, []⟩

/-- Positive example: a stitched dangling cursor keeps flowing through the next factor. -/
example :
    stitchedDangling.childCount = 1 := by
  rfl

/-- Positive example: in the stitched dangling case, descend_until crosses the
boundary in one call. -/
example :
    descendUntilSuffix stitchedDangling = [45, 61] := by
  rfl

/-- Negative example: if the active factor already branches, descend-until does not move. -/
example :
    descendUntilSuffix
      ⟨none, FTrie.node none [(1, FTrie.node (some ()) []), (2, FTrie.node none [])], []⟩ = [] := by
  apply descendUntilSuffix_eq_nil_of_childCount_ne_one
  simp [childCount]

/-! ## Summary

**0 sorries. 0 axioms.**

This file settles the product zipper seam that matters most for Rust:

- stitched boundaries separate value/path-existence from child supply
- explicit observable theorems pin `path_exists`, `is_val`, and `child_count`
- `descend_until` reasons over the active factor's visible children
- movement can cross factor boundaries seamlessly
- stopping still occurs at the first internal value encountered after a stitch
-/

end ProductCursor

end Mettapedia.OSLF.PathMap
