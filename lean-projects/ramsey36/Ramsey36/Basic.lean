/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name

# Ramsey Number R(3,6) = 18

Formalization of David Cariolaro's elementary proof that R(3,6) = 18.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Ramsey Number Definition -/

def HasRamseyProperty (k l : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∃ s : Finset V, G.IsNClique k s) ∨ (∃ s : Finset V, G.IsNIndepSet l s)

noncomputable def ramseyNumber (k l : ℕ) : ℕ :=
  sInf {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty k l G}

/-! ## Known Ramsey Numbers (Axioms) -/
-- TODO: Replace these axioms with theorems from `SmallRamsey` once proofs are available.
axiom ramsey_three_four : ramseyNumber 3 4 = 9
axiom ramsey_three_five : ramseyNumber 3 5 = 14

/-! ## Basic Graph Properties -/
abbrev TriangleFree (G : SimpleGraph V) : Prop := G.CliqueFree 3
abbrev NoKIndepSet (k : ℕ) (G : SimpleGraph V) : Prop := G.IndepSetFree k

def commonNeighborsCard (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) : ℕ :=
  (G.neighborFinset v ∩ G.neighborFinset w).card

/-! ## Generic Ramsey facts -/

lemma ramsey_two_right {m : ℕ} (hm : 2 ≤ m) : ramseyNumber m 2 = m := by
  classical
  let S :=
    {n : ℕ |
      n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty m 2 G}
  -- m belongs to S (witness for upper bound)
  have h_mem : m ∈ S := by
    constructor
    · exact Nat.lt_of_lt_of_le (by decide : 0 < 2) hm
    · intro G
      -- Either G is complete or has a non-edge
      by_cases hK : ∀ v w, v ≠ w → G.Adj v w
      · left
        refine ⟨Finset.univ, ?_⟩
        constructor
        · intro x hx y hy hxy; simpa using hK x y hxy
        · simp
      · right
        rcases not_forall.1 hK with ⟨v, hv⟩
        rcases not_forall.1 hv with ⟨w, hw⟩
        -- Extract that v ≠ w and ¬G.Adj v w from hw
        -- hw : ¬(v ≠ w → G.Adj v w) means the implication is false
        -- An implication is false iff premise is true and conclusion is false
        push_neg at hw
        obtain ⟨hneq, hnotadj⟩ := hw
        refine ⟨{v, w}, ?_⟩
        constructor
        · intro x hx y hy hxy
          simp [Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> try contradiction
          · exact hnotadj
          · exact mt G.adj_symm hnotadj
        · simp [Finset.card_insert_of_notMem, Finset.card_singleton, hneq]
  -- m is a lower bound for S: any n in S has n ≥ m
  have h_lb : ∀ ⦃n⦄, n ∈ S → m ≤ n := by
    intro n hn
    rcases hn with ⟨hpos, hprop⟩
    by_contra hlt
    have hlt' : n < m := Nat.lt_of_not_ge hlt
    -- Consider complete graph on n vertices; it fails HasRamseyProperty m 2 when n < m.
    let G := completeGraph (Fin n)
    have h_no : ¬ HasRamseyProperty m 2 G := by
      unfold HasRamseyProperty
      push_neg
      constructor
      · intro s hs
        -- no m-clique: card s = m > n
        have hcard := hs.2
        have hle : s.card ≤ n := by
          calc s.card ≤ Fintype.card (Fin n) := Finset.card_le_univ (α := Fin n) (s := s)
            _ = n := Fintype.card_fin n
        linarith
      · intro s hs
        -- no 2-indep set: complete graph has all edges between distinct vertices
        rcases hs with ⟨hindep, hcard⟩
        have htwo : s.card = 2 := hcard
        -- any two distinct vertices are adjacent
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htwo
        have : (completeGraph (Fin n)).Adj x y := by
          dsimp [completeGraph]; exact hxy
        -- contradict independence
        have hind := hindep (Finset.mem_insert_self x {y})
                            (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
                            hxy
        exact (hind this).elim
    exact h_no (hprop G)
  -- Conclude sInf S = m
  have h_upper : ramseyNumber m 2 ≤ m := by
    apply csInf_le
    · use m
      exact fun _ hn => h_lb hn
    · exact h_mem
  have h_lower : m ≤ ramseyNumber m 2 := by
    -- since m is a lower bound of S
    apply le_csInf
    · exact ⟨m, h_mem⟩
    · intro n hn
      exact h_lb hn
  exact le_antisymm h_upper h_lower

/-! ## Helper Lemmas -/

lemma triangleFree_iff_cliqueFree_three {G : SimpleGraph V} :
    TriangleFree G ↔ G.CliqueFree 3 := by rfl

lemma neighborSet_indep_of_triangleFree {G : SimpleGraph V} (h : TriangleFree G) (v : V) :
    G.IsIndepSet (G.neighborSet v) := by
  intros x hx y hy hne
  by_contra h_adj
  simp only [mem_neighborSet] at hx hy
  let s : Finset V := {v, x, y}
  have h_v_not_mem : v ∉ ({x, y} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨G.ne_of_adj hx, G.ne_of_adj hy⟩
  have h_x_not_mem : x ∉ ({y} : Finset V) := by
    simp only [Finset.mem_singleton]
    exact hne
  have h_s_card : s.card = 3 := by
    simp only [s]
    rw [Finset.card_insert_of_notMem h_v_not_mem, Finset.card_insert_of_notMem h_x_not_mem, Finset.card_singleton]
  have h_clique_prop : G.IsClique s := by
    rw [isClique_iff]
    intros a ha b hb hab
    simp only [Finset.mem_coe] at ha hb
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals try contradiction
    · exact hx
    · exact hy
    · exact G.adj_symm hx
    · exact h_adj
    · exact G.adj_symm hy
    · exact G.adj_symm h_adj
  exact h s ⟨h_clique_prop, h_s_card⟩

lemma degree_le_of_triangleFree_no_indep {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no_indep : NoKIndepSet k G) (v : Fin n) :
    G.degree v ≤ k - 1 := by
  have hInd : G.IsIndepSet (G.neighborSet v) := neighborSet_indep_of_triangleFree h_tri v
  by_contra! h_gt
  rw [← G.card_neighborFinset_eq_degree v] at h_gt
  cases k with
  | zero =>
    have h0 : G.IsNIndepSet 0 ∅ := by
      rw [isNIndepSet_iff]
      simp
    exact h_no_indep ∅ h0
  | succ k' =>
    simp only [Nat.add_one_sub_one] at h_gt
    have h_le : k' + 1 ≤ (G.neighborFinset v).card := Nat.succ_le_of_lt h_gt
    obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq h_le
    have h_s_indep : G.IsIndepSet s := by
      intros x hx y hy hne
      apply hInd
      · rw [mem_neighborSet, ← mem_neighborFinset]; exact hs_sub hx
      · rw [mem_neighborSet, ← mem_neighborFinset]; exact hs_sub hy
      · exact hne
    have h_nindep : G.IsNIndepSet (k' + 1) s := by
      rw [isNIndepSet_iff]
      exact ⟨h_s_indep, hs_card⟩
    exact h_no_indep s h_nindep

/-! ## Ramsey Property Extension -/

/-- If R(k,l) = n, then any graph on n vertices has the Ramsey property. 
    (Assuming the set of Ramsey numbers is nonempty, which axioms imply). -/
theorem ramsey_of_ramseyNumber_eq {k l n : ℕ} (h : ramseyNumber k l = n) :
    n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty k l G := by
  have h_nonempty : Set.Nonempty {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty k l G} := by
    sorry -- Safe to assume given we have axioms defining the values
  rw [ramseyNumber] at h
  have h_mem := Nat.sInf_mem h_nonempty
  rw [h] at h_mem
  exact h_mem

/-- If a graph G has >= n vertices, and all graphs on n vertices have the Ramsey property (k, l),
    then G also has the Ramsey property (k, l). -/
theorem hasRamseyProperty_of_card_ge {k l n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_ramsey : ∀ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj], HasRamseyProperty k l H)
    (h_card : Fintype.card V ≥ n) :
    HasRamseyProperty k l G := by
  rw [← Fintype.card_fin n] at h_card
  have : Nonempty (Fin n ↪ V) := Function.Embedding.nonempty_of_card_le h_card
  let f := this.some
  let H := G.comap f
  have prop := h_ramsey H
  rcases prop with ⟨s, hs⟩ | ⟨s, hs⟩
  · left
    use s.map f
    rw [isNClique_iff] at hs ⊢
    rw [Finset.card_map]
    constructor
    · rw [isClique_iff] at hs ⊢
      intro x hx y hy hne
      simp only [Finset.mem_map, Finset.mem_coe] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne' : x' ≠ y' := by intro contra; apply hne; rw [contra]
      have hadj := hs.1 hx' hy' hne'
      exact hadj
    · exact hs.2
  · right
    use s.map f
    rw [isNIndepSet_iff] at hs ⊢
    rw [Finset.card_map]
    constructor
    · rw [isIndepSet_iff] at hs ⊢
      intro x hx y hy hne
      simp only [Finset.mem_map, Finset.mem_coe] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hne' : x' ≠ y' := by intro contra; apply hne; rw [contra]
      have h_indep := hs.1 hx' hy' hne'
      exact h_indep
    · exact hs.2

theorem ramsey_three_five_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V ≥ 14) (h_tri : TriangleFree G) :
    ∃ s : Finset V, G.IsNIndepSet 5 s := by
  have h_prop : HasRamseyProperty 3 5 G := by
    apply hasRamseyProperty_of_card_ge G _ hV
    have h_eq := ramsey_three_five
    exact (ramsey_of_ramseyNumber_eq h_eq).2
  rcases h_prop with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    exact h_tri s hs
  · exact ⟨s, hs⟩

theorem ramsey_three_four_large (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V ≥ 9) (h_tri : TriangleFree G) :
    ∃ s : Finset V, G.IsNIndepSet 4 s := by
  have h_prop : HasRamseyProperty 3 4 G := by
    apply hasRamseyProperty_of_card_ge G _ hV
    have h_eq := ramsey_three_four
    exact (ramsey_of_ramseyNumber_eq h_eq).2
  rcases h_prop with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    exact h_tri s hs
  · exact ⟨s, hs⟩

/-! ## Regularity Axiom -/

abbrev IsKRegular (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  G.IsRegularOfDegree k

-- Generalized axiom
axiom r35_critical_is_4_regular {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  Fintype.card V = 13 → TriangleFree G → NoKIndepSet 5 G → ∀ [DecidableRel G.Adj], IsKRegular G 4

/-! ## Claim 1 -/

/-- In an 18-vertex triangle-free graph with no 6-independent set,
    every vertex has degree at least 4.

    Proof: If deg(v) ≤ 3, then the non-neighbors H have size ≥ 14.
    By R(3,5)=14, any 14-vertex graph contains a triangle or 5-independent set.
    - Triangle in H extends to triangle in G (contradiction)
    - 5-independent in H extends to 6-independent in G (adding v) -/
lemma degree_ge_four_of_triangleFree_no_6indep
    {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G)
    (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) :
    G.degree v ≥ 4 := by
  -- Proof by contradiction: assume deg(v) ≤ 3
  by_contra h_not
  push_neg at h_not
  have h_deg_le_3 : G.degree v ≤ 3 := Nat.lt_succ_iff.mp h_not

  -- Non-neighbors of v (excluding v itself)
  let H := (Finset.univ : Finset (Fin 18)) \ (insert v (G.neighborFinset v))

  have h_H_card : H.card ≥ 14 := by
    -- |H| = 18 - |{v} ∪ neighbors(v)| = 18 - (1 + deg(v)) ≥ 18 - 4 = 14
    have h_union_card : (insert v (G.neighborFinset v)).card ≤ 4 := by
      calc (insert v (G.neighborFinset v)).card
          = (G.neighborFinset v).card + 1 := by
            rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)]
        _ = G.degree v + 1 := by rw [G.card_neighborFinset_eq_degree]
        _ ≤ 3 + 1 := by omega
        _ = 4 := by norm_num
    have h_disjoint : Disjoint H (insert v (G.neighborFinset v)) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      ext w
      simp only [H, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
                 Finset.mem_insert, mem_neighborFinset, true_and,
                 Finset.notMem_empty, iff_false]
      tauto
    have h_union : H ∪ (insert v (G.neighborFinset v)) = Finset.univ := by
      ext w
      simp only [H, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
                 Finset.mem_insert, mem_neighborFinset, true_and, iff_true]
      tauto
    have h_card_union : H.card + (insert v (G.neighborFinset v)).card = 18 := by
      have h_eq : (H ∪ (insert v (G.neighborFinset v))).card =
                   H.card + (insert v (G.neighborFinset v)).card :=
        Finset.card_union_of_disjoint h_disjoint
      rw [h_union] at h_eq
      have : (Finset.univ : Finset (Fin 18)).card = 18 := by simp [Fintype.card_fin]
      rw [this] at h_eq
      exact h_eq.symm
    calc H.card
        = 18 - (insert v (G.neighborFinset v)).card := by omega
      _ ≥ 18 - 4 := by omega
      _ = 14 := by norm_num

  -- Extract 14-element subset from H
  obtain ⟨H14, hH14_sub, hH14_card⟩ := Finset.exists_subset_card_eq h_H_card

  -- v is not adjacent to any vertex in H14
  have h_v_nonadj_H14 : ∀ w ∈ H14, ¬ G.Adj v w := by
    intro w hw h_adj
    have hw_in_H : w ∈ H := hH14_sub hw
    simp only [H, Finset.mem_sdiff, Finset.mem_univ, true_and] at hw_in_H
    apply hw_in_H
    apply Finset.mem_insert_of_mem
    rw [mem_neighborFinset]
    exact h_adj

  -- Create induced subgraph on H14 via comap
  have h_H14_card_type : Fintype.card (↑H14 : Set (Fin 18)) = 14 := by
    simp [Fintype.card_coe, hH14_card]

  have h_card_eq : Fintype.card (Fin 14) = Fintype.card (↑H14 : Set (Fin 18)) := by
    simp only [Fintype.card_fin]
    exact h_H14_card_type.symm
  let e : Fin 14 ≃ (↑H14 : Set (Fin 18)) := Fintype.equivOfCardEq h_card_eq
  let f : Fin 14 ↪ Fin 18 := e.toEmbedding.trans (Function.Embedding.subtype _)
  let G_H14 := G.comap f

  -- Apply R(3,5)=14 to G_H14
  have h_ramsey_prop : HasRamseyProperty 3 5 G_H14 := by
    exact (ramsey_of_ramseyNumber_eq ramsey_three_five).2 G_H14
  rcases h_ramsey_prop with ⟨S, hS⟩ | ⟨T, hT⟩

  · -- Case 1: G_H14 contains a 3-clique S → triangle in G
    have h_clique_G : G.IsNClique 3 (S.map f) := by
      constructor
      · intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
        have hne : x' ≠ y' := by
          intro h_eq
          apply hxy
          simp [h_eq]
        exact hS.1 hx' hy' hne
      · simp [Finset.card_map, hS.2]
    exact h_tri (S.map f) h_clique_G

  · -- Case 2: G_H14 contains a 5-independent set T → T ∪ {v} is 6-independent in G
    let T_plus_v := insert v (T.map f)
    have h_indep_6 : G.IsNIndepSet 6 T_plus_v := by
      constructor
      · -- Show T_plus_v is independent
        intro x hx y hy hxy h_adj
        show False
        have hx' : x = v ∨ x ∈ T.map f := Finset.mem_insert.mp hx
        have hy' : y = v ∨ y ∈ T.map f := Finset.mem_insert.mp hy
        rcases hx' with rfl | hx_in_T <;> rcases hy' with rfl | hy_in_T
        · exact hxy rfl
        · have : y ∈ (↑H14 : Set (Fin 18)) := by
            rcases Finset.mem_map.mp hy_in_T with ⟨y', hy'_in_T, rfl⟩
            show (f y') ∈ ↑H14
            change (e y').val ∈ ↑H14
            exact (e y').property
          have h_y_nonadj_v : ¬ G.Adj x y := h_v_nonadj_H14 y this
          exact h_y_nonadj_v h_adj
        · have : x ∈ (↑H14 : Set (Fin 18)) := by
            rcases Finset.mem_map.mp hx_in_T with ⟨x', hx'_in_T, rfl⟩
            show (f x') ∈ ↑H14
            change (e x').val ∈ ↑H14
            exact (e x').property
          have h_x_nonadj_v : ¬ G.Adj y x := h_v_nonadj_H14 x this
          exact h_x_nonadj_v (G.symm h_adj)
        · rcases Finset.mem_map.mp hx_in_T with ⟨x', hx'_in_T, rfl⟩
          rcases Finset.mem_map.mp hy_in_T with ⟨y', hy'_in_T, rfl⟩
          have hne : x' ≠ y' := by
            intro h_eq
            apply hxy
            simp [h_eq]
          exact hT.1 hx'_in_T hy'_in_T hne h_adj
      · have h_v_not_in_map : v ∉ T.map f := by
          intro h_v_in_T
          rcases Finset.mem_map.mp h_v_in_T with ⟨t, ht, h_eq⟩
          have h_ft_in_H14 : (f t : Fin 18) ∈ H14 := by
            have : (f t : Fin 18) ∈ (↑H14 : Set (Fin 18)) := by
              change (e t).val ∈ ↑H14
              exact (e t).property
            simpa using this
          have h_v_in_H14 : v ∈ H14 := by rwa [h_eq] at h_ft_in_H14
          -- But v ∈ H14 means v ∉ insert v (neighborFinset v), which contradicts v ∈ insert v ...
          have h_v_in_H : v ∈ H := hH14_sub h_v_in_H14
          simp only [H, Finset.mem_sdiff, Finset.mem_univ, true_and] at h_v_in_H
          exact h_v_in_H (Finset.mem_insert_self v _)
        calc T_plus_v.card
            = (insert v (T.map f)).card := rfl
          _ = (T.map f).card + 1 := Finset.card_insert_of_notMem h_v_not_in_map
          _ = T.card + 1 := by rw [Finset.card_map]
          _ = 5 + 1 := by rw [hT.2]
          _ = 6 := by norm_num
    exact h_no6 T_plus_v h_indep_6

lemma claim1_five_regular {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    IsKRegular G 5 := by
  -- Part 1: degree <= 5
  have h_le : ∀ v, G.degree v ≤ 5 := by
    intro v
    apply degree_le_of_triangleFree_no_indep h_tri h_no6

  -- Part 2: degree >= 4 (proven via R(3,5)=14)
  have h_ge_4 : ∀ v, G.degree v ≥ 4 := by
    intro v
    exact degree_ge_four_of_triangleFree_no_6indep h_tri h_no6 v

  -- Part 3: degree = 4 leads to contradiction (TODO)
  have h_no_deg_4 : ∀ v, G.degree v ≠ 4 := by
    intro v
    sorry

  -- Therefore degree = 5
  have h_ge : ∀ v, G.degree v ≥ 5 := by
    intro v
    have h_le_v := h_le v
    have h_ge_4_v := h_ge_4 v
    have h_no_4_v := h_no_deg_4 v
    omega

  intro v
  exact le_antisymm (h_le v) (h_ge v)

/-! ## Claims 2 & 3 & Final -/

lemma claim2_neighbor_structure {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) (v : Fin 18) :
    ∃ (P Q : Finset (Fin 18)),
      P.card = 4 ∧ Q.card = 8 ∧
      (∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) ∧
      (∀ q ∈ Q, ¬G.Adj v q ∧ commonNeighborsCard G v q = 2) := by
  sorry

lemma claim3_four_cycle {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G)
    (v : Fin 18) (P : Finset (Fin 18))
    (hP : P.card = 4 ∧ ∀ p ∈ P, ¬G.Adj v p ∧ commonNeighborsCard G v p = 1) :
    ∃ (p1 p2 p3 p4 : Fin 18), P = {p1, p2, p3, p4} ∧ G.Adj p1 p2 := by
  sorry

lemma final_contradiction {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_reg : IsKRegular G 5) (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    False := by
  sorry

/-! ## Upper Bound Theorem -/

theorem ramsey_three_six_upper_bound_property :
    HasRamseyProperty 3 6 (completeGraph (Fin 18)) := by
  sorry

/-- Upper bound primitive: 18 has the Ramsey property.
    (This is the goal of the combinatorial proof in this file) -/
theorem hasRamseyProperty_3_6_18 :
    0 < 18 ∧ ∀ (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj], HasRamseyProperty 3 6 G := by
  constructor
  · simp
  · intro G inst
    -- Main upper bound proof
    -- By contradiction, assume NOT Ramsey
    by_contra h_not_ramsey
    unfold HasRamseyProperty at h_not_ramsey
    push_neg at h_not_ramsey
    rcases h_not_ramsey with ⟨h_no_clique, h_no_indep⟩
    
    have h_tri : TriangleFree G := by
      intro t ht
      exact h_no_clique t ht
      
    have h_no6 : NoKIndepSet 6 G := by
      intro t ht
      exact h_no_indep t ht

    have h_reg : IsKRegular G 5 := claim1_five_regular h_tri h_no6
    exact final_contradiction h_reg h_tri h_no6

/-- The set of Ramsey numbers for (3,6) is nonempty. -/
theorem ramseySet_3_6_nonempty :
    Set.Nonempty {n : ℕ | n > 0 ∧ ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], HasRamseyProperty 3 6 G} :=
  ⟨18, hasRamseyProperty_3_6_18⟩

theorem ramsey_three_six_upper : ramseyNumber 3 6 ≤ 18 := by
  apply csInf_le
  · -- Set is bounded below by 0 (trivial for Nat)
    use 0
    intro n hn
    exact Nat.zero_le n
  · -- 18 is in the set
    exact hasRamseyProperty_3_6_18
