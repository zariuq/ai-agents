import Mettapedia.OSLF.PathMap.Trie.CoinductiveTrie
import Mettapedia.OSLF.PathMap.Trie.FiniteTrie
import Mettapedia.OSLF.PathMap.Trie.MeetSubtractRefinement
import Mettapedia.OSLF.PathMap.Trie.MeetSubtractSorted
import Mettapedia.OSLF.PathMap.Trie.TrieRefinement

/-!
# Meet Refinement — `FTrie.meet` ↪ `CTrie.inter`

This file upgrades `meet` from root-only agreement to full pathwise lookup
refinement, using the same sorted-child merge discipline as `join`.
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u

namespace FTrie

variable {V : Type u}

private theorem uint8_eq_not_lt (a b : UInt8) (h1 : ¬ (a < b)) (h2 : ¬ (b < a)) :
    a = b := by
  rw [UInt8.lt_iff_toNat_lt] at h1 h2
  rw [Nat.not_lt] at h1 h2
  exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.le_antisymm h2 h1))

@[simp] theorem normalize_lookup_cons (t : FTrie V) (b : UInt8) (rest : List UInt8) :
    t.normalize.lookup (b :: rest) = t.lookup (b :: rest) := by
  cases t with
  | empty =>
      rfl
  | node val children =>
      cases val <;> cases children <;> simp [FTrie.normalize, FTrie.lookup]

theorem lookupChild_none_of_meetChildren (b : UInt8) (rest : List UInt8)
    (cs₁ cs₂ : List (UInt8 × FTrie V))
    (h₁ : ∀ p ∈ cs₁, b < p.1) (h₂ : ∀ p ∈ cs₂, b < p.1) :
    lookupChild b rest (meetChildren cs₁ cs₂) = none := by
  exact lookupChild_none_of_forall_lt b rest (meetChildren cs₁ cs₂)
    (fun p hp => mc_gt b cs₁ cs₂ h₁ h₂ p hp)

mutual
  theorem meet_lookup (t₁ t₂ : FTrie V) (p : List UInt8)
      (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
      (t₁.meet t₂).lookup p =
        (match t₁.lookup p, t₂.lookup p with
         | some v, some _ => some v
         | _, _ => none) := by
    cases t₁ with
    | empty =>
        cases t₂ <;> cases p <;> simp [FTrie.meet, FTrie.lookup]
    | node v₁ c₁ =>
      cases t₂ with
      | empty =>
          cases p <;> simp [FTrie.meet, FTrie.lookup]
      | node v₂ c₂ =>
          cases p with
          | nil =>
              simpa using meet_lookup_nil (FTrie.node v₁ c₁) (FTrie.node v₂ c₂)
          | cons b rest =>
              have ⟨hpw₁, hcs₁⟩ := h₁
              have ⟨hpw₂, hcs₂⟩ := h₂
              cases v₁ with
              | none =>
                  cases v₂ with
                  | none =>
                      have hchild := meetChildren_lookup c₁ c₂ b rest hpw₁ hpw₂ hcs₁ hcs₂
                      calc
                        ((FTrie.node none c₁).meet (FTrie.node none c₂)).lookup (b :: rest)
                            = (FTrie.node none (FTrie.meetChildren c₁ c₂)).normalize.lookup (b :: rest) := by
                                simp [FTrie.meet]
                  _ = (FTrie.node none (FTrie.meetChildren c₁ c₂)).lookup (b :: rest) := by
                              exact normalize_lookup_cons
                                (FTrie.node none (FTrie.meetChildren c₁ c₂)) b rest
                        _ = lookupChild b rest (FTrie.meetChildren c₁ c₂) := by
                              simp [FTrie.lookup]
                        _ = (match lookupChild b rest c₁, lookupChild b rest c₂ with
                             | some v, some _ => some v
                             | _, _ => none) := hchild
                  | some v₂' =>
                      have hchild := meetChildren_lookup c₁ c₂ b rest hpw₁ hpw₂ hcs₁ hcs₂
                      calc
                        ((FTrie.node none c₁).meet (FTrie.node (some v₂') c₂)).lookup (b :: rest)
                            = (FTrie.node none (FTrie.meetChildren c₁ c₂)).normalize.lookup (b :: rest) := by
                                simp [FTrie.meet]
                  _ = (FTrie.node none (FTrie.meetChildren c₁ c₂)).lookup (b :: rest) := by
                              exact normalize_lookup_cons
                                (FTrie.node none (FTrie.meetChildren c₁ c₂)) b rest
                        _ = lookupChild b rest (FTrie.meetChildren c₁ c₂) := by
                              simp [FTrie.lookup]
                        _ = (match lookupChild b rest c₁, lookupChild b rest c₂ with
                             | some v, some _ => some v
                             | _, _ => none) := hchild
              | some v₁' =>
                  cases v₂ with
                  | none =>
                      have hchild := meetChildren_lookup c₁ c₂ b rest hpw₁ hpw₂ hcs₁ hcs₂
                      calc
                        ((FTrie.node (some v₁') c₁).meet (FTrie.node none c₂)).lookup (b :: rest)
                            = (FTrie.node none (FTrie.meetChildren c₁ c₂)).normalize.lookup (b :: rest) := by
                                simp [FTrie.meet]
                  _ = (FTrie.node none (FTrie.meetChildren c₁ c₂)).lookup (b :: rest) := by
                              exact normalize_lookup_cons
                                (FTrie.node none (FTrie.meetChildren c₁ c₂)) b rest
                        _ = lookupChild b rest (FTrie.meetChildren c₁ c₂) := by
                              simp [FTrie.lookup]
                        _ = (match lookupChild b rest c₁, lookupChild b rest c₂ with
                             | some v, some _ => some v
                             | _, _ => none) := hchild
                  | some v₂' =>
                      simpa [FTrie.meet, FTrie.lookup] using
                        meetChildren_lookup c₁ c₂ b rest hpw₁ hpw₂ hcs₁ hcs₂

  theorem meetChildren_lookup
      (cs₁ cs₂ : List (UInt8 × FTrie V))
      (b : UInt8) (rest : List UInt8)
      (hpw₁ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₁)
      (hpw₂ : List.Pairwise (fun a c : UInt8 × FTrie V => a.1 < c.1) cs₂)
      (hcs₁ : childrenSorted cs₁) (hcs₂ : childrenSorted cs₂) :
      lookupChild b rest (meetChildren cs₁ cs₂) =
        (match lookupChild b rest cs₁, lookupChild b rest cs₂ with
         | some v, some _ => some v
         | _, _ => none) := by
    match cs₁, cs₂ with
    | [], _ =>
        simp [FTrie.meetChildren, lookupChild_nil']
    | (b₁, t₁) :: rest₁, [] =>
        simp [FTrie.meetChildren, lookupChild_nil']
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
        unfold FTrie.meetChildren
        have hpw₁' := (List.pairwise_cons.mp hpw₁).2
        have hall₁ := (List.pairwise_cons.mp hpw₁).1
        have hpw₂' := (List.pairwise_cons.mp hpw₂).2
        have hall₂ := (List.pairwise_cons.mp hpw₂).1
        have ⟨hs₁, hcs₁'⟩ := hcs₁
        have ⟨hs₂, hcs₂'⟩ := hcs₂
        split
        · rename_i hlt₁
          by_cases hb : b = b₁
          · subst hb
            rw [lookupChild_cons_eq _ t₁ _ _ _ rfl]
            have hnone :
                lookupChild b rest ((b₂, t₂) :: rest₂) = none :=
              lookupChild_none_of_forall_lt b rest ((b₂, t₂) :: rest₂) (fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hp
                · exact hlt₁
                · exact Trans.trans hlt₁ (hall₂ p hp))
            rw [hnone]
            rw [lookupChild_none_of_meetChildren b rest rest₁ ((b₂, t₂) :: rest₂)
              (fun p hp => hall₁ p hp)
              (fun p hp => by
                rcases List.mem_cons.mp hp with rfl | hm
                · exact hlt₁
                · exact Trans.trans hlt₁ (hall₂ p hm))]
            cases t₁.lookup rest <;> rfl
          · rw [lookupChild_cons_ne _ t₁ _ _ _ (Ne.symm hb)]
            exact meetChildren_lookup rest₁ ((b₂, t₂) :: rest₂) b rest hpw₁' hpw₂ hcs₁' hcs₂
        · split
          · rename_i _ hlt₂
            by_cases hb : b = b₂
            · subst hb
              rw [lookupChild_cons_eq _ t₂ _ _ _ rfl]
              have hnone :
                  lookupChild b rest ((b₁, t₁) :: rest₁) = none :=
                lookupChild_none_of_forall_lt b rest ((b₁, t₁) :: rest₁) (fun p hp => by
                  rcases List.mem_cons.mp hp with rfl | hp
                  · exact hlt₂
                  · exact Trans.trans hlt₂ (hall₁ p hp))
              rw [hnone]
              rw [lookupChild_none_of_meetChildren b rest ((b₁, t₁) :: rest₁) rest₂
                (fun p hp => by
                  rcases List.mem_cons.mp hp with rfl | hm
                  · exact hlt₂
                  · exact Trans.trans hlt₂ (hall₁ p hm))
                (fun p hp => hall₂ p hp)]
            · rw [lookupChild_cons_ne _ t₂ _ _ _ (Ne.symm hb)]
              exact meetChildren_lookup ((b₁, t₁) :: rest₁) rest₂ b rest hpw₁ hpw₂' hcs₁ hcs₂'
          · rename_i hnlt₁ hnlt₂
            have heq : b₁ = b₂ := uint8_eq_not_lt _ _ hnlt₁ hnlt₂
            subst heq
            by_cases hb : b = b₁
            · subst hb
              rw [lookupChild_cons_eq _ t₁ _ _ _ rfl, lookupChild_cons_eq _ t₂ _ _ _ rfl]
              cases hm : t₁.meet t₂ with
              | empty =>
                  rw [lookupChild_none_of_meetChildren b rest rest₁ rest₂
                    (fun p hp => hall₁ p hp) (fun p hp => hall₂ p hp)]
                  have ih := meet_lookup t₁ t₂ rest hs₁ hs₂
                  rw [hm] at ih
                  simpa [FTrie.lookup_empty] using ih
              | node v cs =>
                  rw [lookupChild_cons_eq _ (FTrie.node v cs) _ _ _ rfl]
                  have ih := meet_lookup t₁ t₂ rest hs₁ hs₂
                  rw [hm] at ih
                  exact ih
            · rw [lookupChild_cons_ne _ t₁ _ _ _ (Ne.symm hb),
                  lookupChild_cons_ne _ t₂ _ _ _ (Ne.symm hb)]
              cases hm : t₁.meet t₂ with
              | empty =>
                  exact meetChildren_lookup rest₁ rest₂ b rest hpw₁' hpw₂' hcs₁' hcs₂'
              | node v cs =>
                  rw [lookupChild_cons_ne _ (FTrie.node v cs) _ _ _ (Ne.symm hb)]
                  exact meetChildren_lookup rest₁ rest₂ b rest hpw₁' hpw₂' hcs₁' hcs₂'
end

theorem toCTrie_meet (t₁ t₂ : FTrie V) (h₁ : t₁.Sorted) (h₂ : t₂.Sorted) :
    CTrie.Bisim (t₁.meet t₂).toCTrie (CTrie.inter t₁.toCTrie t₂.toCTrie) :=
  fun p => by
    simpa [CTrie.lookup_inter] using meet_lookup t₁ t₂ p h₁ h₂

end FTrie

end Mettapedia.OSLF.PathMap.Trie
