import Mettapedia.GSLT.Meredith.LambdaTheory
import Mettapedia.OSLF.Framework.ModalHypercube

/-!
# Rewrite Modalities: §5.4 of "Generating Hypercubes of Type Systems"

Formalization of the modal type formers generated from base rewrites
and redex positions in a lambda theory.

## Main Definitions

* `RedexPosition` — a choice of subterm and one-hole context in a base rewrite (§5.4)
* `ModalitySlots` — the local sort slots for a modality (§5.6)
* `ModalTyping` — the typing judgment extended with modal types:
  - `M-Form`: formation rule for ⟨K_j⟩ modalities
  - `M-Intro`: introduction from typing the reduct under relies
  - `M-Step`: elimination yielding operational step
  - `M-Elim⇝`: elimination yielding typing of the reduct

## Key Insight (§5.4)

Each base rewrite `L(x̄) ⇝ R(x̄)` and each subterm position `t_j ⊆ L`
generates a modality `⟨K_j⟩_{x̄ :: Ā} B` at carrier `Y_j`, where:
- `K_j[−]` is the one-hole context with `K_j[t_j] = L`
- `V_j = FV(K_j) \ FV(t_j)` — the "rely" variables
- The modality asserts: under rely assumptions, placing `t` in `K_j[−]`
  takes one step to `R(x̄)` which inhabits `B`.

## References

- Stay, Meredith & Wells, "Generating Hypercubes of Type Systems" (2026), §5.4
-/

namespace Mettapedia.GSLT.Meredith.Modal

open Mettapedia.GSLT.Meredith
open Mettapedia.OSLF.Framework.ModalHypercube

/-! ## Redex Positions (§5.4) -/

/-- A redex position in a base rewrite.

    §5.4: "Choose any subterm occurrence t_j ⊆ L with carrier Y_j and
    one-holed context K_j[−] (so that K_j[t_j] = L)."

    We represent this abstractly: a redex position selects a subterm of
    the left-hand side and a one-hole context that reconstructs it.

    * `relyArity` — number of rely variables: |V_j| = |FV(K_j) \ FV(t_j)|
    * `subterm` — the selected subterm t_j (as a morphism in context)
    * `context` — the one-hole context K_j[−] (as a function filling the hole)
    * `fills` — K_j[t_j] = L (the context applied to the subterm gives the LHS)
-/
structure RedexPosition (T : LambdaTheory) (br : BaseRewrite T) where
  /-- The carrier of the subterm (Y_j in the paper). -/
  subtermCarrier : T.Obj
  /-- Number of rely parameters: variables free in K_j but not in t_j. -/
  relyArity : ℕ
  /-- The subterm t_j : ctx ⟶ Y_j (projected from the base rewrite context). -/
  subterm : br.ctx ⟶ subtermCarrier
  /-- The one-hole context K_j[−]: given a term of carrier Y_j, produces a process.
      §5.4: K_j is a one-hole context with K_j[t_j] = L. -/
  fillContext : (br.ctx ⟶ subtermCarrier) → (br.ctx ⟶ T.Pr)
  /-- K_j[t_j] = L: the context applied to the subterm gives the LHS. -/
  fills : fillContext subterm = br.lhs

/-! ## Sort Slots for Modalities (§5.6) -/

/-- The sort slot family for a modality at a given redex position.

    §5.6: "Each modality ⟨K_j⟩ carries its own slot family
    Slots(K_j, B) := {s^{X_k}_k}_{k ∈ V_j} ∪ {s_out}."

    Total number of slots = relyArity + 1 (rely inputs + one output).
-/
def modalitySlotCount (relyArity : ℕ) : ℕ := relyArity + 1

/-- The output slot index (last slot). -/
def outputSlot (relyArity : ℕ) : Fin (modalitySlotCount relyArity) :=
  ⟨relyArity, Nat.lt_succ_of_le (Nat.le_refl _)⟩

/-- A rely slot index (for the k-th rely parameter). -/
def relySlot {relyArity : ℕ} (k : Fin relyArity) : Fin (modalitySlotCount relyArity) :=
  ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩

/-! ## Modal Typing Judgment (§5.4) -/

/-- A modal type specification: the data needed to form a modal type ⟨K_j⟩_{x̄::Ā} B.

    This bundles a redex position with sort assignments for each slot.
    §5.4: The modality `⟨K_j⟩_{x̄::Ā} B` is a type former at carrier Y_j
    carrying one sort slot per rely input and one output slot.
-/
structure ModalTypeSpec (T : LambdaTheory) where
  /-- The underlying base rewrite. -/
  baseRewrite : BaseRewrite T
  /-- The chosen redex position. -/
  position : RedexPosition T baseRewrite
  /-- Sort assignment for each slot (rely inputs + output). -/
  sortAssignment : Fin (modalitySlotCount position.relyArity) → HSort

/-! ## Formation, Introduction, and Elimination

    We define these as propositions (judgment forms) rather than inductive types,
    since the full typing judgment requires the ambient lambda theory's
    type-theoretic structure which we keep abstract.
-/

/-- **M-Form**: The modality ⟨K_j⟩_{x̄::Ā} B is well-formed when each
    rely type A_k is well-sorted and the postcondition B is well-sorted.

    §5.4.1: "The modality ⟨K_j⟩_{x̄::Ā} B is a type former at carrier Y_j."
-/
structure ModalFormation (spec : ModalTypeSpec T) : Prop where
  /-- Each rely type former A_k has the correct sort at its carrier. -/
  relySorted : ∀ k : Fin spec.position.relyArity,
    spec.sortAssignment (relySlot k) = spec.sortAssignment (relySlot k)
    -- Tautological here; in the full system this would check A_k :: s^{X_k}_k
  /-- The postcondition B has the output sort. -/
  postSorted : True
    -- In the full system: B :: s^Pr_out

/-- **M-Intro**: Introduction rule for ⟨K_j⟩.

    §5.4.2: "Introduction types the chosen redex component t_j by demanding
    that the specified right-hand side has the desired type under the relies."

    Abstractly: if we can show R(x̄) :: B under the rely assumptions,
    then t_j :: ⟨K_j⟩_{x̄::Ā} B.
-/
structure ModalIntro (T : LambdaTheory) (spec : ModalTypeSpec T) : Prop where
  /-- The RHS R(x̄) is well-typed at B under rely assumptions.
      This is the core semantic content of introduction. -/
  rhsTyped : True  -- Abstract: ∀ rely instances satisfying Ā, R(ū) :: B[ū/x̄]

/-- **M-Step**: Elimination yielding operational step.

    §5.4.3: "Step to the specified RHS":
    ```
    Γ Δ ⊢ t :: ⟨K_j⟩_{x̄::Ā} B    Γ Δ ⊢ u_k :: A_k
    ────────────────────────────────────────────────────
    Γ Δ ⊢ K_j[t][ū/x̄] ⇝ R(ū)
    ```
-/
structure ModalStep (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br) : Prop where
  /-- The operational step fires: K_j[t][ū/x̄] ⇝ R(ū). -/
  steps : T.rewriteRel (pos.fillContext pos.subterm) br.rhs
  -- This follows directly from pos.fills and br.fires

/-- M-Step is derivable from the base rewrite and the context fill. -/
theorem modalStep_from_base (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br) : ModalStep T br pos where
  steps := pos.fills ▸ br.fires

/-- **M-Elim⇝**: Elimination yielding typing of the reduct.

    §5.4.3: "Typing of the specified RHS":
    ```
    Γ Δ ⊢ t :: ⟨K_j⟩_{x̄::Ā} B    Γ Δ ⊢ u_k :: A_k
    ────────────────────────────────────────────────────
    Γ Δ ⊢ R(ū) :: B[ū/x̄]
    ```

    This is the typing half of elimination — the reduct is well-typed.
-/
structure ModalElimTyping (T : LambdaTheory) (spec : ModalTypeSpec T) : Prop where
  /-- The reduct R(ū) has the postcondition type B[ū/x̄]. -/
  reductTyped : True  -- Abstract: R(ū) :: B[ū/x̄]

/-! ## Rely-Possibly Reading (§5.4.4)

    "The type former ⟨K_j⟩_{x̄::Ā} B is interpreted as the comprehension
    of those t : Y_j that satisfy:
      ∀(x_k : X_k). (∧ x_k :: ⟦A_k⟧) ⇒ K_j(t) ⇝ R(x̄) ∧ R(x̄) :: ⟦B⟧"

    This semantic reading unifies the step and typing eliminations.
-/

/-- The rely-possibly semantic reading of a modal type.

    §5.4.4: membership in the modality provides both
    (i) a step to the specified RHS, and
    (ii) typing information about that RHS.
-/
structure RelyPossiblyReading (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br) : Prop where
  /-- (i) Operational step: K_j[t] ⇝ R(x̄) -/
  hasStep : ModalStep T br pos
  /-- (ii) Typing: R(x̄) is well-typed -/
  hasTyping : True  -- Abstract typing condition

/-- The rely-possibly reading follows from M-Step. -/
theorem relyPossibly_from_base (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br) : RelyPossiblyReading T br pos where
  hasStep := modalStep_from_base T br pos
  hasTyping := trivial

end Mettapedia.GSLT.Meredith.Modal
