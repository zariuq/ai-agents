import FourColor.KempeAPI
import FourColor.Triangulation
import FourColor.Geometry.Disk
import Mathlib.Data.Finset.Card
import Mathlib.Order.WellFounded

/-!
# Kempe Chain Reachability - Existence of Proper Zero-Boundary Chains

This module proves the key lemma `exists_proper_zero_boundary`: among all zero-boundary
chains (which by Lemma 4.5 are spanned by face boundaries), at least one encodes a
proper 3-edge-coloring.

## Main Result

`exists_proper_zero_boundary`: Given any nontrivial zero-boundary chain, we can reach
a proper one via Kempe switches.

## Proof Strategy (Solution A: Lexicographic Descent)

We use well-founded induction on the lexicographic measure `(#bad, #supp)` where:
- `#bad` = number of vertices where properness fails
- `#supp` = size of the support (edges with nonzero color)

At each step, we perform a Kempe switch at a bad vertex. Either:
1. The number of bad vertices strictly decreases, or
2. The number of bad vertices stays the same, but H2+H3 give us a toggle that
   strictly decreases support while preserving zero-boundary.

## References

- Goertzel (2025), Section 4: Disk Kempe-Closure Spanning
- Strategic Roadmap: `STRATEGIC_ROADMAP_2025-11-01.md`
- User guidance: Solution A from final user message

-/

namespace FourColor

open Classical Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (D : ZeroBoundaryData V E)

/-- Lexicographic measure for well-founded descent -/
def measurePair (x : E → Color) : ℕ × ℕ :=
  ((badVerts D.incident x).card, (supp x).card)

/-- The lexicographic ordering on ℕ × ℕ is well-founded -/
lemma wf_measurePair : WellFounded (fun x y : E → Color => measurePair D x < measurePair D y) :=
  measure_wf (measurePair D)

/-- If not proper, there exists a bad vertex -/
lemma exists_bad {x : E → Color} (hn : ¬taitProper D.incident x) :
    ∃ v, v ∈ badVerts D.incident x := by
  classical
  unfold taitProper at hn
  push_neg at hn
  obtain ⟨v, hv⟩ := hn
  use v
  simp [mem_badVerts]
  exact hv

/-- Core descent lemma: Kempe switch either decreases bad-count or support -/
lemma kempe_or_support_descent
    {x : E → Color}
    (hx : InZero D x)
    (hnz : (supp x).Nonempty)
    {v : V}
    (hbad : v ∈ badVerts D.incident x) :
    let x' := kempeFix D.incident x v
    (badVerts D.incident x').card < (badVerts D.incident x).card
    ∨ ((badVerts D.incident x').card = (badVerts D.incident x).card
        ∧ (supp x').card < (supp x).card) := by
  classical
  sorry  -- This is where we use H2+H3
  /-
  Proof outline:
  1. The Kempe switch at v either:
     a) Fixes v and creates no new bad vertices → bad-count drops
     b) Fixes v but might create new bad vertices
  2. In case (b), use H2 (exists prescribed cut S₀ in support) to find a toggle
  3. Use H3 (toggle S₀ strictly decreases support) to reduce support
  4. The toggle preserves zero-boundary by sum-closure lemmas
  5. Return the disjunction based on which case occurred

  The detailed proof requires:
  - kempeSwitch local analysis (you already proved this for kempeSwitch_preserves_proper)
  - H2: exists_prescribed_cut from Disk.lean
  - H3: toggle_strict_decrease from Disk.lean
  - sum_mem_zero from Triangulation.lean
  -/

/-- Main existence theorem via well-founded recursion -/
theorem exists_proper_zero_boundary
    (x₀ : E → Color)
    (hx₀ : InZero D x₀)
    (hnz : (supp x₀).Nonempty) :
    ∃ x : E → Color, InZero D x ∧ taitProper D.incident x := by
  classical
  -- Use well-founded recursion on the lexicographic measure
  -- We build the result using WellFounded.fix with a sigma type to thread InZero through

  let motive : (E → Color) → Type := fun x =>
    { y : E → Color // InZero D y ∧ taitProper D.incident y }

  have step : ∀ x : E → Color,
    (∀ y, measurePair D y < measurePair D x → motive y) →
    motive x := by
    intro x IH
    -- Check if x is already proper
    by_cases hp : taitProper D.incident x
    · -- Base case: x is proper
      exact ⟨x, sorry, hp⟩  -- TODO: need to show InZero D x from context
    · -- Recursive case: x is not proper
      -- Find a bad vertex
      obtain ⟨v, hv⟩ := exists_bad D (x := x) hp
      -- Perform Kempe switch
      let x' := kempeFix D.incident x v
      -- x' preserves zero-boundary
      have hx'_zero : InZero D x' := sorry  -- Will use kempeFix_preserves_zero
      -- Measure decreases
      have hdesc := kempe_or_support_descent D (x := x) (v := v)
                      (hx := sorry) (hnz := sorry) (hbad := hv)
      have hlt : measurePair D x' < measurePair D x := by
        rcases hdesc with hbadDrop | ⟨heq, hsuppDrop⟩
        · -- Bad-count dropped
          constructor
          · exact hbadDrop
          · exact Nat.le_refl _
        · -- Support dropped
          constructor
          · rw [heq]; exact Nat.le_refl _
          · exact hsuppDrop
      -- Apply inductive hypothesis
      exact IH x' hlt

  -- Apply well-founded recursion
  have result := WellFounded.fix (wf_measurePair D) step x₀
  exact ⟨result.val, result.property⟩

/-
TODO: Fill the sorries by:
1. Threading InZero through the recursion (use sigma type return)
2. Wiring kempeFix_preserves_zero from KempeAPI
3. Completing kempe_or_support_descent using H2+H3
4. The three small context sorries in the step function
-/

end FourColor
