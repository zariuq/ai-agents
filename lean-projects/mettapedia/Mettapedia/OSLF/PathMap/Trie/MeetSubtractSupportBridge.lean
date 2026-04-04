import Mettapedia.OSLF.PathMap.Trie.RestrictSupportBridge
import Mettapedia.OSLF.PathMap.Trie.MeetRefinement
import Mettapedia.OSLF.PathMap.Trie.SubtractRefinement
import Mettapedia.OSLF.PathMap.Trie.MeetSubtractSorted

/-!
# Meet/Subtract Support Bridge

Proves the extensional support-level equalities:
- `pathSupport (t₁.meet t₂) = pathSupport t₁ ∩ pathSupport t₂`
- `pathSupport (t₁.subtract t₂) = pathSupport t₁ \ pathSupport t₂`

Uses `meet_lookup` from MeetRefinement.lean and `subtract_lookup` from
SubtractRefinement.lean, bridged to `pathSupport` via helpers from
RestrictSupportBridge.lean.

## Rust Impact

These theorems give oracle tests for meet/subtract immediately:
compute `pathSupport` on both sides and compare against `∩` / `\`.
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

/-! ## §1: Meet Support = Intersection -/

/-- **Meet support = intersection** (for sorted Unit tries).

    Positive example: `{[1,2], [3]}` meet `{[1,2], [4]}` = `{[1,2]}`
    Negative example: paths in only one trie are excluded. -/
theorem pathSupport_meet_eq_inter (t₁ t₂ : FTrie Unit)
    (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    pathSupport (t₁.meet t₂) = pathSupport t₁ ∩ pathSupport t₂ := by
  have hm := FTrie.meet_sorted t₁ t₂ h₁ h₂
  ext p
  simp only [Finset.mem_inter]
  constructor
  · -- p ∈ meet support → p ∈ both
    intro hp
    have hlookup := lookup_of_pathSupport_mem _ p hm hp
    rw [meet_lookup t₁ t₂ p h₁ h₂] at hlookup
    cases h1 : t₁.lookup p <;> cases h2 : t₂.lookup p <;> simp_all
    exact ⟨pathSupport_mem_of_lookup _ _ h1, pathSupport_mem_of_lookup _ _ h2⟩
  · -- p ∈ both → p ∈ meet support
    intro ⟨hp₁, hp₂⟩
    have h1 := lookup_of_pathSupport_mem _ p h₁ hp₁
    have h2 := lookup_of_pathSupport_mem _ p h₂ hp₂
    have hmeet : (t₁.meet t₂).lookup p = some () := by
      rw [meet_lookup t₁ t₂ p h₁ h₂, h1, h2]
    exact pathSupport_mem_of_lookup _ _ hmeet

/-! ## §2: Subtract Support = Set Difference -/

/-- **Subtract support = set difference** (for sorted Unit tries).

    Positive example: `{[1,2], [3]}` subtract `{[1,2]}` = `{[3]}`
    Negative example: paths in the rhs are removed from the result. -/
theorem pathSupport_subtract_eq_sdiff (t₁ t₂ : FTrie Unit)
    (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    pathSupport (t₁.subtract t₂) = pathSupport t₁ \ pathSupport t₂ := by
  have hs := FTrie.subtract_sorted t₁ t₂ h₁ h₂
  ext p
  simp only [Finset.mem_sdiff]
  constructor
  · -- p ∈ subtract support → p ∈ lhs and p ∉ rhs
    intro hp
    have hlookup := lookup_of_pathSupport_mem _ p hs hp
    rw [subtract_lookup t₁ t₂ p h₁ h₂] at hlookup
    cases h1 : t₁.lookup p <;> cases h2 : t₂.lookup p <;> simp_all
    constructor
    · exact pathSupport_mem_of_lookup _ _ h1
    · intro habs
      have := lookup_of_pathSupport_mem _ p h₂ habs
      simp_all
  · -- p ∈ lhs, p ∉ rhs → p ∈ subtract support
    intro ⟨hp₁, hp₂⟩
    have h1 := lookup_of_pathSupport_mem _ p h₁ hp₁
    have h2 : t₂.lookup p = none := by
      by_contra habs
      push_neg at habs
      cases hv : t₂.lookup p with
      | none => contradiction
      | some v =>
        cases v
        exact hp₂ (pathSupport_mem_of_lookup _ _ hv)
    have hsub : (t₁.subtract t₂).lookup p = some () := by
      rw [subtract_lookup t₁ t₂ p h₁ h₂, h1, h2]
    exact pathSupport_mem_of_lookup _ _ hsub

/-! ## §3: Summary

**0 sorries. 0 axioms.**

| Theorem | What it says |
|---------|-------------|
| `pathSupport_meet_eq_inter` | meet support = lhs ∩ rhs |
| `pathSupport_subtract_eq_sdiff` | subtract support = lhs \ rhs |

Together with `RestrictSupportBridge.pathSupport_restrict_eq_restrictPaths`
and the join support theorem from UnitBridge, all four PathMap algebra
operations now have extensional support characterization.

Maps to Rust: oracle tests for meet/subtract compare `pathSupport` on
both sides against `BTreeSet::intersection` / `BTreeSet::difference`.
-/

end Mettapedia.OSLF.PathMap.Trie
