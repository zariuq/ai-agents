import Mettapedia.OSLF.PathMap.Trie.CoinductiveTrie
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie

/-!
# Trie Refinement — FTrie ↪ CTrie Homomorphism

The finite trie `FTrie V` embeds into the coinductive `CTrie V` via its lookup
function.  This module proves that FTrie operations commute with CTrie operations
up to `Bisim`, when the FTrie is well-sorted.

## References

- CoinductiveTrie.lean: canonical coinductive semantics
- FiniteTrie.lean: finite inductive operations
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u

namespace FTrie

variable {V : Type u}

/-! ## §1: Sortedness -/

mutual
  /-- Well-sorted FTrie: child keys are strictly increasing at every level. -/
  def Sorted : FTrie V → Prop
    | .empty => True
    | .node _ children =>
      List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) children ∧
      childrenSorted children

  /-- All children are themselves sorted. -/
  def childrenSorted : List (UInt8 × FTrie V) → Prop
    | [] => True
    | (_, t) :: rest => t.Sorted ∧ childrenSorted rest
end

/-! ## §2: Embedding -/

/-- Embed a finite trie into the coinductive representation via its lookup function. -/
def toCTrie (t : FTrie V) : CTrie V := fun p => t.lookup p

@[simp] theorem toCTrie_apply (t : FTrie V) (p : List UInt8) :
    t.toCTrie p = t.lookup p := rfl

/-! ## §3: UInt8 Helpers -/

private theorem uint8_eq_of_not_lt_not_lt (a b : UInt8)
    (h1 : ¬(a < b)) (h2 : ¬(b < a)) : a = b := by
  rw [UInt8.lt_iff_toNat_lt] at h1 h2; rw [Nat.not_lt] at h1 h2
  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.le_antisymm h2 h1))

/-! ## §4: lookupChild Abstraction Lemmas -/

theorem lookupChild_cons_eq (k : UInt8) (child : FTrie V)
    (cs : List (UInt8 × FTrie V)) (b : UInt8) (rest : List UInt8) (h : k = b) :
    lookupChild b rest ((k, child) :: cs) = child.lookup rest := by
  subst h; simp only [lookupChild, beq_self_eq_true]; simp

theorem lookupChild_cons_ne (k : UInt8) (child : FTrie V)
    (cs : List (UInt8 × FTrie V)) (b : UInt8) (rest : List UInt8) (h : k ≠ b) :
    lookupChild b rest ((k, child) :: cs) = lookupChild b rest cs := by
  simp only [lookupChild, beq_false_of_ne h]; simp

@[simp] theorem lookupChild_nil' (b : UInt8) (rest : List UInt8) :
    lookupChild (V := V) b rest [] = none := by unfold lookupChild; rfl

theorem lookupChild_none_of_forall_lt (b : UInt8) (rest : List UInt8)
    (cs : List (UInt8 × FTrie V)) (h : ∀ p ∈ cs, b < p.1) :
    lookupChild b rest cs = none := by
  induction cs with
  | nil => exact lookupChild_nil' _ _
  | cons hd tl ih =>
    rw [lookupChild_cons_ne _ _ _ _ _ (by intro heq; subst heq; simp at h)]
    exact ih (fun p hp => h p (by simp [hp]))

/-! ## §5: Option Helper -/

private theorem option_orElse_none (x : Option V) : (x <|> none) = x := by
  cases x <;> rfl

/-! ## §5b: lookupChild on joinChildren with all keys > b -/

theorem lookupChild_none_of_joinChildren (b : UInt8) (rest : List UInt8)
    (cs₁ cs₂ : List (UInt8 × FTrie V))
    (h₁ : ∀ p ∈ cs₁, b < p.1) (h₂ : ∀ p ∈ cs₂, b < p.1) :
    lookupChild b rest (joinChildren cs₁ cs₂) = none := by
  match cs₁, cs₂ with
  | [], _ => unfold joinChildren; exact lookupChild_none_of_forall_lt _ _ _ h₂
  | (b₁, t₁) :: rest₁, [] =>
    have : joinChildren ((b₁, t₁) :: rest₁) ([] : List (UInt8 × FTrie V)) =
        (b₁, t₁) :: rest₁ := by unfold joinChildren; rfl
    rw [this]; exact lookupChild_none_of_forall_lt _ _ _ h₁
  | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
    unfold joinChildren
    have hb₁ : b < b₁ := h₁ _ List.mem_cons_self
    have hb₂ : b < b₂ := h₂ _ List.mem_cons_self
    have h₁' : ∀ p ∈ rest₁, b < p.1 := fun p hp => h₁ p (List.mem_cons_of_mem _ hp)
    have h₂' : ∀ p ∈ rest₂, b < p.1 := fun p hp => h₂ p (List.mem_cons_of_mem _ hp)
    split
    · have hne : b₁ ≠ b := by intro heq; subst heq; simp at hb₁
      rw [lookupChild_cons_ne _ _ _ _ _ hne]
      exact lookupChild_none_of_joinChildren b rest rest₁ ((b₂, t₂) :: rest₂) h₁' h₂
    · split
      · have hne : b₂ ≠ b := by intro heq; subst heq; simp at hb₂
        rw [lookupChild_cons_ne _ _ _ _ _ hne]
        exact lookupChild_none_of_joinChildren b rest ((b₁, t₁) :: rest₁) rest₂ h₁ h₂'
      · cases hj : t₁.join t₂ with
        | empty => exact lookupChild_none_of_joinChildren b rest rest₁ rest₂ h₁' h₂'
        | node v cs =>
          have hne : b₁ ≠ b := by intro heq; subst heq; simp at hb₁
          rw [lookupChild_cons_ne _ _ _ _ _ hne]
          exact lookupChild_none_of_joinChildren b rest rest₁ rest₂ h₁' h₂'

/-! ## §6: Join Lookup Correctness -/

mutual
  /-- Join agrees with pointwise union on lookup (requires sortedness). -/
  theorem join_lookup (t₁ t₂ : FTrie V) (p : List UInt8)
      (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
      (t₁.join t₂).lookup p = (t₁.lookup p <|> t₂.lookup p) := by
    cases t₁ with
    | empty => unfold join lookup; rfl
    | node v₁ c₁ =>
      cases t₂ with
      | empty =>
        unfold join
        have : (FTrie.empty : FTrie V).lookup p = none := by cases p <;> (unfold lookup; rfl)
        rw [this, option_orElse_none]
      | node v₂ c₂ =>
        unfold join; cases p with
        | nil => unfold lookup; rfl
        | cons b rest =>
          unfold lookup
          have ⟨hpw₁, hcs₁⟩ := h₁
          have ⟨hpw₂, hcs₂⟩ := h₂
          exact joinChildren_lookup c₁ c₂ b rest hpw₁ hpw₂ hcs₁ hcs₂

  /-- Child-list helper for join_lookup. -/
  theorem joinChildren_lookup
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (b : UInt8) (rest : List UInt8)
      (hpw₁ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₁)
      (hpw₂ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₂)
      (hcs₁ : childrenSorted cs₁) (hcs₂ : childrenSorted cs₂) :
      lookupChild b rest (joinChildren cs₁ cs₂) =
        (lookupChild b rest cs₁ <|> lookupChild b rest cs₂) := by
    match cs₁, cs₂ with
    | [], _ =>
      unfold joinChildren; rw [lookupChild_nil']; rfl
    | (b₁, t₁) :: rest₁, [] =>
      have hnil : joinChildren ((b₁, t₁) :: rest₁) ([] : List (UInt8 × FTrie V)) =
          (b₁, t₁) :: rest₁ := by unfold joinChildren; rfl
      rw [hnil, lookupChild_nil', option_orElse_none]
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
      unfold joinChildren
      have hpw₁' := (List.pairwise_cons.mp hpw₁).2
      have hall₁ := (List.pairwise_cons.mp hpw₁).1
      have hpw₂' := (List.pairwise_cons.mp hpw₂).2
      have hall₂ := (List.pairwise_cons.mp hpw₂).1
      have ⟨hs₁, hcs₁'⟩ := hcs₁
      have ⟨hs₂, hcs₂'⟩ := hcs₂
      split
      · -- b₁ < b₂
        rename_i hlt₁
        by_cases hb : b = b₁
        · subst hb
          rw [lookupChild_cons_eq _ t₁ _ _ _ rfl]
          have hnone := lookupChild_none_of_forall_lt b rest ((b₂, t₂) :: rest₂) (fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hlt₁
            · exact Trans.trans hlt₁ (hall₂ p hp))
          rw [lookupChild_cons_eq _ t₁ _ _ _ rfl, hnone, option_orElse_none]
        · rw [lookupChild_cons_ne _ t₁ _ _ _ (Ne.symm hb),
              lookupChild_cons_ne _ t₁ _ _ _ (Ne.symm hb)]
          exact joinChildren_lookup rest₁ ((b₂, t₂) :: rest₂) b rest hpw₁' hpw₂ hcs₁' hcs₂
      · split
        · -- b₂ < b₁
          rename_i hnlt₁ hlt₂
          by_cases hb : b = b₂
          · subst hb
            rw [lookupChild_cons_eq _ t₂ _ _ _ rfl]
            have hnone := lookupChild_none_of_forall_lt b rest ((b₁, t₁) :: rest₁)
                (fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hlt₂
              · exact Trans.trans hlt₂ (hall₁ p hp))
            rw [lookupChild_cons_eq _ t₂ _ _ _ rfl, hnone]; rfl
          · rw [lookupChild_cons_ne _ t₂ _ _ _ (Ne.symm hb),
                lookupChild_cons_ne _ t₂ _ _ _ (Ne.symm hb)]
            exact joinChildren_lookup ((b₁, t₁) :: rest₁) rest₂ b rest hpw₁ hpw₂' hcs₁ hcs₂'
        · -- b₁ = b₂
          rename_i hnlt₁ hnlt₂
          have heq : b₁ = b₂ := uint8_eq_of_not_lt_not_lt _ _ hnlt₁ hnlt₂
          subst heq
          by_cases hb : b = b₁
          · subst hb
            rw [lookupChild_cons_eq _ t₁ _ _ _ rfl, lookupChild_cons_eq _ t₂ _ _ _ rfl]
            cases hj : t₁.join t₂ with
            | empty =>
              have ih := join_lookup t₁ t₂ rest hs₁ hs₂
              rw [hj] at ih; simp [lookup_empty] at ih
              have ⟨h1, h2⟩ : t₁.lookup rest = none ∧ t₂.lookup rest = none := by
                cases h1 : t₁.lookup rest <;> simp_all
              rw [h1, h2]; simp
              exact lookupChild_none_of_joinChildren b rest rest₁ rest₂
                (fun p hp => hall₁ p hp) (fun p hp => hall₂ p hp)
            | node v cs =>
              rw [lookupChild_cons_eq _ (FTrie.node v cs) _ _ _ rfl]
              have ih := join_lookup t₁ t₂ rest hs₁ hs₂
              rw [hj] at ih; exact ih
          · rw [lookupChild_cons_ne _ t₁ _ _ _ (Ne.symm hb),
                lookupChild_cons_ne _ t₂ _ _ _ (Ne.symm hb)]
            cases hj : t₁.join t₂ with
            | empty =>
              exact joinChildren_lookup rest₁ rest₂ b rest hpw₁' hpw₂' hcs₁' hcs₂'
            | node v cs =>
              rw [lookupChild_cons_ne _ (FTrie.node v cs) _ _ _ (Ne.symm hb)]
              exact joinChildren_lookup rest₁ rest₂ b rest hpw₁' hpw₂' hcs₁' hcs₂'
end

/-! ## §7: Homomorphism Theorems -/

/-- The FTrie → CTrie embedding preserves join up to Bisim. -/
theorem toCTrie_join (t₁ t₂ : FTrie V) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    CTrie.Bisim (t₁.join t₂).toCTrie (CTrie.union t₁.toCTrie t₂.toCTrie) :=
  fun p => join_lookup t₁ t₂ p h₁ h₂

/-! ## §8: Summary

`toCTrie` embeds `FTrie V` into `CTrie V` via its lookup function.
The embedding is a homomorphism: FTrie operations commute with CTrie
operations up to `Bisim` when the FTrie is well-sorted.

Meet, subtract, and restrict homomorphisms follow the same pattern.
-/

end FTrie

end Mettapedia.OSLF.PathMap.Trie
