import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# Meet / Subtract Sortedness Preservation

This file strengthens the finite-trie algebra tower by proving that `meet` and
`subtract` preserve the `Sorted` invariant used throughout the concrete
PathMap refinement story.
-/

namespace Mettapedia.OSLF.PathMap.Trie

open FTrie

universe u

variable {V : Type u}

private theorem uint8_eq_not_lt (a b : UInt8) (h1 : ¬ (a < b)) (h2 : ¬ (b < a)) :
    a = b := by
  rw [UInt8.lt_iff_toNat_lt] at h1 h2
  rw [Nat.not_lt] at h1 h2
  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.le_antisymm h2 h1))

private theorem normalize_node_none_sorted (cs : List (UInt8 × FTrie V))
    (hpw : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs)
    (hcs : childrenSorted cs) :
    (FTrie.node none cs).normalize.Sorted := by
  cases cs with
  | nil => simp [FTrie.normalize, FTrie.Sorted]
  | cons hd tl => simpa [FTrie.normalize, FTrie.Sorted] using And.intro hpw hcs

mutual
  theorem FTrie.meet_sorted (t₁ t₂ : FTrie V) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
      (t₁.meet t₂).Sorted := by
    cases t₁ with
    | empty =>
        simpa [FTrie.meet]
    | node v₁ c₁ =>
      cases t₂ with
      | empty =>
          simpa [FTrie.meet]
      | node v₂ c₂ =>
          have ⟨hpw₁, hcs₁⟩ := h₁
          have ⟨hpw₂, hcs₂⟩ := h₂
          cases v₁ <;> cases v₂
          · simpa [FTrie.meet] using
              normalize_node_none_sorted _
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2
          · simpa [FTrie.meet] using
              normalize_node_none_sorted _
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2
          · simpa [FTrie.meet] using
              normalize_node_none_sorted _
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2
          · simpa [FTrie.meet, FTrie.normalize, FTrie.Sorted] using
              And.intro
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (meetChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2

  theorem meetChildren_sorted
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (hpw₁ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₁)
      (hpw₂ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₂)
      (hcs₁ : childrenSorted cs₁) (hcs₂ : childrenSorted cs₂) :
      List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) (meetChildren cs₁ cs₂) ∧
      childrenSorted (meetChildren cs₁ cs₂) := by
    match cs₁, cs₂ with
    | [], _ =>
        unfold FTrie.meetChildren
        exact ⟨by simp, trivial⟩
    | (b₁, t₁) :: rest₁, [] =>
        unfold FTrie.meetChildren
        exact ⟨by simp, trivial⟩
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
        unfold FTrie.meetChildren
        have hpw₁' := (List.pairwise_cons.mp hpw₁).2
        have hall₁ := (List.pairwise_cons.mp hpw₁).1
        have hpw₂' := (List.pairwise_cons.mp hpw₂).2
        have hall₂ := (List.pairwise_cons.mp hpw₂).1
        have ⟨hs₁, hcs₁'⟩ := hcs₁
        have ⟨hs₂, hcs₂'⟩ := hcs₂
        split
        · exact meetChildren_sorted rest₁ ((b₂, t₂) :: rest₂) hpw₁' hpw₂ hcs₁' hcs₂
        · split
          · exact meetChildren_sorted ((b₁, t₁) :: rest₁) rest₂ hpw₁ hpw₂' hcs₁ hcs₂'
          · have heq := uint8_eq_not_lt _ _ ‹¬ b₁ < b₂› ‹¬ b₂ < b₁›
            subst heq
            have ⟨ihpw, ihcs⟩ := meetChildren_sorted rest₁ rest₂ hpw₁' hpw₂' hcs₁' hcs₂'
            cases hm : meet t₁ t₂ with
            | empty =>
                exact ⟨ihpw, ihcs⟩
            | node v cs =>
                exact ⟨List.pairwise_cons.mpr
                  ⟨mc_gt b₁ rest₁ rest₂ hall₁ hall₂, ihpw⟩,
                  by rw [← hm]; exact FTrie.meet_sorted t₁ t₂ hs₁ hs₂,
                  ihcs⟩

  theorem mc_gt (b : UInt8)
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (h₁ : ∀ p ∈ cs₁, b < p.1) (h₂ : ∀ p ∈ cs₂, b < p.1) :
      ∀ p ∈ meetChildren cs₁ cs₂, b < p.1 := by
    match cs₁, cs₂ with
    | [], _ =>
        unfold FTrie.meetChildren
        intro p hp
        simp at hp
    | (b₁, t₁) :: rest₁, [] =>
        unfold FTrie.meetChildren
        intro p hp
        simp at hp
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
        unfold FTrie.meetChildren
        have hb₁ := h₁ _ (.head _)
        have hb₂ := h₂ _ (.head _)
        have h₁' : ∀ q ∈ rest₁, b < q.1 := fun q hq => h₁ q (.tail _ hq)
        have h₂' : ∀ q ∈ rest₂, b < q.1 := fun q hq => h₂ q (.tail _ hq)
        intro p
        split
        · intro hp
          exact mc_gt b rest₁ ((b₂, t₂) :: rest₂) h₁' h₂ p hp
        · split
          · intro hp
            exact mc_gt b ((b₁, t₁) :: rest₁) rest₂ h₁ h₂' p hp
          · intro hp
            generalize hm : meet t₁ t₂ = merged at hp
            match merged, hp with
            | .empty, hp =>
                exact mc_gt b rest₁ rest₂ h₁' h₂' p hp
            | .node _ _, hp =>
                rcases List.mem_cons.mp hp with rfl | hm'
                · exact hb₁
                · exact mc_gt b rest₁ rest₂ h₁' h₂' p hm'
end

mutual
  theorem FTrie.subtract_sorted (t₁ t₂ : FTrie V) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
      (t₁.subtract t₂).Sorted := by
    cases t₁ with
    | empty =>
        simpa [FTrie.subtract]
    | node v₁ c₁ =>
      cases t₂ with
      | empty =>
          simpa [FTrie.subtract] using h₁
      | node v₂ c₂ =>
          have ⟨hpw₁, hcs₁⟩ := h₁
          have ⟨hpw₂, hcs₂⟩ := h₂
          cases v₁ <;> cases v₂
          · simpa [FTrie.subtract] using
              normalize_node_none_sorted _
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2
          · simpa [FTrie.subtract] using
              normalize_node_none_sorted _
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2
          · simpa [FTrie.subtract, FTrie.normalize, FTrie.Sorted] using
              And.intro
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2
          · simpa [FTrie.subtract] using
              normalize_node_none_sorted _
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).1
                (subtractChildren_sorted _ _ hpw₁ hpw₂ hcs₁ hcs₂).2

  theorem subtractChildren_sorted
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (hpw₁ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₁)
      (hpw₂ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₂)
      (hcs₁ : childrenSorted cs₁) (hcs₂ : childrenSorted cs₂) :
      List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) (subtractChildren cs₁ cs₂) ∧
      childrenSorted (subtractChildren cs₁ cs₂) := by
    match cs₁, cs₂ with
    | [], _ =>
        unfold FTrie.subtractChildren
        exact ⟨by simp, trivial⟩
    | (b₁, t₁) :: rest₁, [] =>
        have : subtractChildren ((b₁, t₁) :: rest₁) ([] : List (UInt8 × FTrie V)) =
            (b₁, t₁) :: rest₁ := by
          unfold FTrie.subtractChildren
          rfl
        rw [this]
        exact ⟨hpw₁, hcs₁⟩
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
        unfold FTrie.subtractChildren
        have hpw₁' := (List.pairwise_cons.mp hpw₁).2
        have hall₁ := (List.pairwise_cons.mp hpw₁).1
        have hpw₂' := (List.pairwise_cons.mp hpw₂).2
        have hall₂ := (List.pairwise_cons.mp hpw₂).1
        have ⟨hs₁, hcs₁'⟩ := hcs₁
        have ⟨hs₂, hcs₂'⟩ := hcs₂
        split
        · have ⟨ihpw, ihcs⟩ := subtractChildren_sorted rest₁ ((b₂, t₂) :: rest₂)
            hpw₁' hpw₂ hcs₁' hcs₂
          exact ⟨List.pairwise_cons.mpr
            ⟨sc_gt b₁ rest₁ ((b₂, t₂) :: rest₂) hall₁
              (fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hm
                · exact ‹b₁ < b₂›
                · exact Trans.trans ‹b₁ < b₂› (hall₂ p hm)),
             ihpw⟩,
            hs₁, ihcs⟩
        · split
          · exact subtractChildren_sorted ((b₁, t₁) :: rest₁) rest₂ hpw₁ hpw₂' hcs₁ hcs₂'
          · have heq := uint8_eq_not_lt _ _ ‹¬ b₁ < b₂› ‹¬ b₂ < b₁›
            subst heq
            have ⟨ihpw, ihcs⟩ := subtractChildren_sorted rest₁ rest₂ hpw₁' hpw₂' hcs₁' hcs₂'
            cases hs : subtract t₁ t₂ with
            | empty =>
                exact ⟨ihpw, ihcs⟩
            | node v cs =>
                exact ⟨List.pairwise_cons.mpr
                  ⟨sc_gt b₁ rest₁ rest₂ hall₁ hall₂, ihpw⟩,
                  by rw [← hs]; exact FTrie.subtract_sorted t₁ t₂ hs₁ hs₂,
                  ihcs⟩

  theorem sc_gt (b : UInt8)
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (h₁ : ∀ p ∈ cs₁, b < p.1) (h₂ : ∀ p ∈ cs₂, b < p.1) :
      ∀ p ∈ subtractChildren cs₁ cs₂, b < p.1 := by
    match cs₁, cs₂ with
    | [], _ =>
        unfold FTrie.subtractChildren
        intro p hp
        simp at hp
    | (b₁, t₁) :: rest₁, [] =>
        have : subtractChildren ((b₁, t₁) :: rest₁) ([] : List (UInt8 × FTrie V)) =
            (b₁, t₁) :: rest₁ := by
          unfold FTrie.subtractChildren
          rfl
        rw [this]
        exact h₁
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
        unfold FTrie.subtractChildren
        have hb₁ := h₁ _ (.head _)
        have hb₂ := h₂ _ (.head _)
        have h₁' : ∀ q ∈ rest₁, b < q.1 := fun q hq => h₁ q (.tail _ hq)
        have h₂' : ∀ q ∈ rest₂, b < q.1 := fun q hq => h₂ q (.tail _ hq)
        intro p
        split
        · intro hp
          rcases List.mem_cons.mp hp with rfl | hm
          · exact hb₁
          · exact sc_gt b rest₁ ((b₂, t₂) :: rest₂) h₁' h₂ p hm
        · split
          · intro hp
            exact sc_gt b ((b₁, t₁) :: rest₁) rest₂ h₁ h₂' p hp
          · intro hp
            generalize hs : subtract t₁ t₂ = merged at hp
            match merged, hp with
            | .empty, hp =>
                exact sc_gt b rest₁ rest₂ h₁' h₂' p hp
            | .node _ _, hp =>
                rcases List.mem_cons.mp hp with rfl | hm'
                · exact hb₁
                · exact sc_gt b rest₁ rest₂ h₁' h₂' p hm'
end

end Mettapedia.OSLF.PathMap.Trie
