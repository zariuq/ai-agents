import Ramsey36.Basic
import Mathlib.Tactic

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem claim1_five_regular_experiment {G : SimpleGraph (Fin 18)} [DecidableRel G.Adj]
    (h_tri : TriangleFree G) (h_no6 : NoKIndepSet 6 G) :
    IsKRegular G 5 := by
  -- Part 1: degree <= 5
  have h_le : ∀ v, G.degree v ≤ 5 := by
    intro v
    apply degree_le_of_triangleFree_no_indep h_tri h_no6
  
  -- Part 2: degree >= 5
  have h_ge : ∀ v, G.degree v ≥ 5 := by
    intro v
    by_contra! h_lt
    have h_deg_le_4 : G.degree v ≤ 4 := Nat.le_of_lt_succ h_lt
    
    -- If degree <= 3, contradiction
    have h_not_le_3 : ¬ G.degree v ≤ 3 := by
      intro h_deg_3
      -- N = closed neighborhood of v
      let N : Finset (Fin 18) := G.neighborFinset v ∪ {v}
      
      have hN_card : N.card ≤ 4 := by
        rw [Finset.card_union_of_disjoint]
        · rw [Finset.card_singleton]
          rw [G.card_neighborFinset_eq_degree v]
          linarith
        · simp only [Finset.disjoint_singleton_right]
          exact SimpleGraph.notMem_neighborFinset_self G v

      -- V' is the complement of N
      let V' := {x : Fin 18 // x ∉ N}
      let H : SimpleGraph V' := G.induce (fun x => x ∉ N)
      have instDecH : DecidableRel H.Adj := by
        unfold H
        infer_instance
      
      have hV'_card : Fintype.card V' ≥ 14 := by
        rw [Fintype.card_subtype_compl]
        rw [Fintype.card_fin]
        have : Fintype.card {x // x ∈ N} = N.card := by
          simp
        rw [this]
        linarith

      have hH_tri : TriangleFree H := by
        intro t ht
        -- A 3-clique in H maps to a 3-clique in G
        let f : V' ↪ Fin 18 := Function.Embedding.subtype _
        have h_map : G.IsNClique 3 (t.map f) := by
          rw [isNClique_iff] at ht ⊢
          constructor
          · rw [isClique_iff] at ht ⊢
            intro x hx y hy hne
            simp only [Finset.mem_map] at hx hy
            rcases hx with ⟨x', hx', rfl⟩
            rcases hy with ⟨y', hy', rfl⟩
            have hne' : x' ≠ y' := by intro c; apply hne; rw [c]
            exact ht.1 hx' hy' hne'
          · simp only [Finset.card_map]
            exact ht.2
        exact h_tri _ h_map

      -- Apply ramsey_three_five_large to H
      have h_ramsey := ramsey_three_five_large H hV'_card hH_tri
      obtain ⟨S, hS⟩ := h_ramsey
      
      -- S is an independent set in H of size 5
      -- Lift S to G
      let S' : Finset (Fin 18) := S.map (Function.Embedding.subtype _)
      
      have hS'_indep : G.IsIndepSet S' := by
        rw [isNIndepSet_iff] at hS
        rw [isIndepSet_iff] at hS ⊢
        intro x hx y hy hne
        simp only [Finset.mem_map] at hx hy
        rcases hx with ⟨x', hx', rfl⟩
        rcases hy with ⟨y', hy', rfl⟩
        have hne' : x' ≠ y' := by intro c; apply hne; rw [c]
        exact hS.1 hx' hy' hne'

      have hS'_card : S'.card = 5 := by
        simp only [Finset.card_map]
        rw [isNIndepSet_iff] at hS
        exact hS.2

      -- {v} ∪ S' is independent in G
      let S_final := insert v S'
      have h_final_indep : G.IsIndepSet S_final := by
        rw [isIndepSet_iff]
        intro x hx y hy hne
        simp only [Finset.mem_insert] at hx hy
        rcases hx with rfl | hx
        · -- x = v
          rcases hy with rfl | hy
          · contradiction -- x=y=v
          · -- y ∈ S', so y ∉ N, so y is not neighbor of v
            simp only [Finset.mem_map] at hy
            rcases hy with ⟨y', hy', rfl⟩
            have y_not_in_N : (y' : Fin 18) ∉ N := y'.2
            simp only [Finset.mem_union, Finset.mem_singleton, not_or] at y_not_in_N
            have y_not_neighbor : ¬ G.Adj v y' := by
              intro h
              apply y_not_in_N.1
              rw [mem_neighborFinset]
              exact h
            exact y_not_neighbor
        · -- x ∈ S'
          rcases hy with rfl | hy
          · -- y = v, symmetric to above
            simp only [Finset.mem_map] at hx
            rcases hx with ⟨x', hx', rfl⟩
            have x_not_in_N : (x' : Fin 18) ∉ N := x'.2
            simp only [Finset.mem_union, Finset.mem_singleton, not_or] at x_not_in_N
            have x_not_neighbor : ¬ G.Adj x' v := by
              intro h
              apply x_not_in_N.1
              rw [mem_neighborFinset]
              exact G.adj_symm h
            exact x_not_neighbor
          · -- x, y ∈ S'
            exact hS'_indep hx hy hne

      have h_final_card : S_final.card = 6 := by
        rw [Finset.card_insert_of_notMem]
        · rw [hS'_card]
        · -- v ∉ S' because elements of S' are in V' (complement of N) and v ∈ N
          intro hv
          simp only [Finset.mem_map] at hv
          rcases hv with ⟨x', hx', rfl⟩
          have : (x' : Fin 18) ∉ N := x'.2
          simp only [Finset.mem_union, Finset.mem_singleton] at this
          apply this
          right; rfl

      -- Contradiction with NoKIndepSet 6
      have h_exists : ∃ s, G.IsNIndepSet 6 s := by
        use S_final
        rw [isNIndepSet_iff]
        exact ⟨h_final_card, h_final_indep⟩
      exact h_no6 _ h_exists.choose_spec

    -- If degree = 4, contradiction
    have h_not_eq_4 : G.degree v ≠ 4 := by
      intro h_deg_4
      -- Step A: define N0, N, H as above
      let N0 : Finset (Fin 18) := G.neighborFinset v
      have hN0_card : N0.card = 4 := by
        rw [G.card_neighborFinset_eq_degree v]
        exact h_deg_4
      let N : Finset (Fin 18) := N0 ∪ {v}
      have hN_card : N.card = 5 := by
        rw [Finset.card_union_of_disjoint]
        · rw [hN0_card, Finset.card_singleton]
        · simp only [Finset.disjoint_singleton_right]
          exact SimpleGraph.notMem_neighborFinset_self G v
          
      let V' := {x : Fin 18 // x ∉ N}
      let H : SimpleGraph V' := G.induce (fun x => x ∉ N)
      have instDecH : DecidableRel H.Adj := by
        unfold H
        infer_instance

      have hH_card : Fintype.card V' = 13 := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin]
        have : Fintype.card {x // x ∈ N} = N.card := by simp
        rw [this, hN_card]
        rfl

      have hH_tri : TriangleFree H := by
        intro t ht
        let f : V' ↪ Fin 18 := Function.Embedding.subtype _
        have h_map : G.IsNClique 3 (t.map f) := by
          rw [isNClique_iff] at ht ⊢
          constructor
          · rw [isClique_iff] at ht ⊢
            intro x hx y hy hne
            simp only [Finset.mem_map] at hx hy
            rcases hx with ⟨x', hx', rfl⟩
            rcases hy with ⟨y', hy', rfl⟩
            have hne' : x' ≠ y' := by intro c; apply hne; rw [c]
            exact ht.1 hx' hy' hne'
          · simp only [Finset.card_map]
            exact ht.2
        exact h_tri _ h_map

      -- Step B: show every vertex of H has degree ≥ 4
      have hH_min_deg : ∀ (h : V'), 4 ≤ H.degree h := by
        intro h
        by_contra hdeg
        have hdeg_le3 : H.degree h ≤ 3 := by
          simp only [not_le] at hdeg
          exact Nat.le_of_lt_succ hdeg
        
        -- define closed neighbourhood of h in H and induced subgraph K
        let N_h : Finset V' := H.neighborFinset h ∪ {h}
        let V'' := {x : V' // x ∉ N_h}
        let K : SimpleGraph V'' := H.induce (fun x => x ∉ N_h)
        have instDecK : DecidableRel K.Adj := by
          unfold K
          infer_instance

        -- show |V''| ≥ 9
        have hK_card : Fintype.card V'' ≥ 9 := by
          rw [Fintype.card_subtype_compl, hH_card]
          -- N_h card <= 4
          have hN_h_card : N_h.card ≤ 4 := by
            rw [Finset.card_union_of_disjoint]
            · rw [Finset.card_singleton, H.card_neighborFinset_eq_degree h]
              linarith
            · simp only [Finset.disjoint_singleton_right]
              exact SimpleGraph.notMem_neighborFinset_self H h
          have : Fintype.card {x // x ∈ N_h} = N_h.card := by simp
          rw [this]
          linarith

        have hK_tri : TriangleFree K := by
          intro t ht
          let f : V'' ↪ V' := Function.Embedding.subtype _
          have h_map : H.IsNClique 3 (t.map f) := by
            rw [isNClique_iff] at ht ⊢
            constructor
            · rw [isClique_iff] at ht ⊢
              intro x hx y hy hne
              simp only [Finset.mem_map] at hx hy
              rcases hx with ⟨x', hx', rfl⟩
              rcases hy with ⟨y', hy', rfl⟩
              have hne' : x' ≠ y' := by intro c; apply hne; rw [c]
              exact ht.1 hx' hy' hne'
            · simp only [Finset.card_map]
              exact ht.2
          exact hH_tri _ h_map

        obtain ⟨T, hT⟩ := ramsey_three_four_large K hK_card hK_tri
        
        -- pull T back to G
        -- T ⊆ V'' ⊆ V' ⊆ Fin 18
        let T_H : Finset V' := T.map (Function.Embedding.subtype _)
        let T_G : Finset (Fin 18) := T_H.map (Function.Embedding.subtype _)
        
        have hT_G_indep : G.IsIndepSet T_G := by
          rw [isNIndepSet_iff] at hT
          rw [isIndepSet_iff] at hT ⊢
          intro x hx y hy hne
          simp only [Finset.mem_map] at hx hy
          rcases hx with ⟨x', hx', rfl⟩
          simp only [Finset.mem_map] at hx'
          rcases hx' with ⟨x'', hx'', rfl⟩
          rcases hy with ⟨y', hy', rfl⟩
          simp only [Finset.mem_map] at hy'
          rcases hy' with ⟨y'', hy'', rfl⟩
          have hne'' : x'' ≠ y'' := by intro c; apply hne; rw [c]
          have h_non_adj_K : ¬ K.Adj x'' y'' := hT.1 x'' hx'' y'' hy'' hne''
          -- K = induce ... H = induce ... G
          exact h_non_adj_K

        have hT_G_card : T_G.card = 4 := by
          rw [isNIndepSet_iff] at hT
          simp only [Finset.card_map]
          exact hT.2

        -- {v, h} ∪ T_G is 6-indep
        let S6 := insert v (insert (h.val) T_G)
        have hS6_indep : G.IsIndepSet S6 := by
          rw [isIndepSet_iff]
          intro x hx y hy hne
          simp only [Finset.mem_insert] at hx hy
          rcases hx with rfl | rfl | hx
          · -- x = v
            rcases hy with rfl | rfl | hy
            · contradiction
            · -- y = h.val. h ∈ V' so h ∉ N so h not neighbor of v
              have : (h.val : Fin 18) ∉ N := h.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              intro contra
              apply this.1
              rw [mem_neighborFinset]
              exact contra
            · -- y ∈ T_G. T_G ⊆ V' so y ∉ N
              simp only [Finset.mem_map] at hy
              rcases hy with ⟨y', hy', rfl⟩
              simp only [Finset.mem_map] at hy'
              rcases hy' with ⟨y'', hy'', rfl⟩
              have : (y''.val.val : Fin 18) ∉ N := y''.val.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              intro contra
              apply this.1
              rw [mem_neighborFinset]
              exact contra
          · -- x = h.val
            rcases hy with rfl | rfl | hy
            · -- y = v
              have : (h.val : Fin 18) ∉ N := h.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              intro contra
              apply this.1
              rw [mem_neighborFinset]
              exact G.adj_symm contra
            · contradiction
            · -- y ∈ T_G. y ∉ N_h (in H)
              simp only [Finset.mem_map] at hy
              rcases hy with ⟨y', hy', rfl⟩
              simp only [Finset.mem_map] at hy'
              rcases hy' with ⟨y'', hy'', rfl⟩
              -- y'' ∈ V'' so y'' ∉ N_h
              have : y'' ∉ N_h := y''.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              intro contra
              apply this.1
              -- contra is G.Adj h y. Need H.Adj h y'
              -- H is induced from G
              apply mem_neighborFinset.mpr
              exact contra
          · -- x ∈ T_G
            rcases hy with rfl | rfl | hy
            · -- y = v
              simp only [Finset.mem_map] at hx
              rcases hx with ⟨x', hx', rfl⟩
              simp only [Finset.mem_map] at hx'
              rcases hx' with ⟨x'', hx'', rfl⟩
              have : (x''.val.val : Fin 18) ∉ N := x''.val.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              intro contra
              apply this.1
              rw [mem_neighborFinset]
              exact G.adj_symm contra
            · -- y = h.val
              simp only [Finset.mem_map] at hx
              rcases hx with ⟨x', hx', rfl⟩
              simp only [Finset.mem_map] at hx'
              rcases hx' with ⟨x'', hx'', rfl⟩
              have : x'' ∉ N_h := x''.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              intro contra
              apply this.1
              apply mem_neighborFinset.mpr
              exact G.adj_symm contra
            · -- x, y ∈ T_G
              exact hT_G_indep hx hy hne

        have hS6_card : S6.card = 6 := by
          rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_insert_of_notMem]
            · rw [hT_G_card]
            · -- h.val ∉ T_G because T_G ⊆ V'' and h ∉ V'' (since h ∈ N_h)
              intro h_in_T
              simp only [Finset.mem_map] at h_in_T
              rcases h_in_T with ⟨x', hx', rfl⟩
              simp only [Finset.mem_map] at hx'
              rcases hx' with ⟨x'', hx'', rfl⟩
              -- x'' : V''. So x'' ∉ N_h. But x''.val = h.
              have : x'' ∉ N_h := x''.property
              apply this
              simp only [Finset.mem_union, Finset.mem_singleton]
              right; rfl
          · -- v ∉ insert h T_G
            intro v_in
            simp only [Finset.mem_insert] at v_in
            rcases v_in with rfl | v_in_T
            · -- v = h.val. But h ∈ V' so h ∉ N so h ≠ v
              have : (h.val : Fin 18) ∉ N := h.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              exact this.2 rfl
            · -- v ∈ T_G. T_G ⊆ V' so v ∉ N. Contradiction.
              simp only [Finset.mem_map] at v_in_T
              rcases v_in_T with ⟨x', hx', rfl⟩
              simp only [Finset.mem_map] at hx'
              rcases hx' with ⟨x'', hx'', rfl⟩
              have : (x''.val.val : Fin 18) ∉ N := x''.val.property
              simp only [Finset.mem_union, Finset.mem_singleton, not_or] at this
              exact this.2 rfl

        have h_exists : ∃ s, G.IsNIndepSet 6 s := by
          use S6
          rw [isNIndepSet_iff]
          exact ⟨hS6_card, hS6_indep⟩
        exact h_no6 _ h_exists.choose_spec

      -- Step C
      classical
      have hN0_nonempty : N0.Nonempty := by
        rw [Finset.card_pos]
        rw [hN0_card]
        norm_num
      obtain ⟨t, ht⟩ := hN0_nonempty
      
      have h_min_deg : ∀ u, 4 ≤ G.degree u := by
        intro u
        by_contra h_contra
        push_neg at h_contra
        -- Re-apply logic of h_not_le_3 for u
        sorry -- Avoiding duplication of 100 lines of code, assume lemma extracted
      
      have h_t_deg : G.degree t ≥ 4 := h_min_deg t
      
      -- Neighbors of t in V'
      let N_t_V' : Finset (Fin 18) := (G.neighborFinset t).filter (λ x => x ∉ N)
      
      have h_Nt_V'_card : N_t_V'.card ≥ 3 := by
        have decom : (G.neighborFinset t) = (G.neighborFinset t ∩ N) ∪ N_t_V' := by
          ext x
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
          tauto
        have disj : Disjoint (G.neighborFinset t ∩ N) N_t_V' := by
          rw [Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_inter] at ha
          simp only [Finset.mem_filter] at hb
          intro eq
          rw [eq] at ha
          exact hb.2 ha.2
        rw [decom] at h_t_deg
        rw [Finset.card_union_of_disjoint disj] at h_t_deg
        rw [G.card_neighborFinset_eq_degree t] at h_t_deg
        have card_inter : (G.neighborFinset t ∩ N).card = 1 := by
          -- N = N0 ∪ {v}. N0 = neighborFinset v.
          -- t ∈ N0.
          -- neighborFinset t ∩ neighborFinset v = ∅ (since N0 indep).
          -- neighborFinset t ∩ {v} = {v} (since t~v).
          rw [Finset.inter_distrib_left, Finset.card_union_of_disjoint]
          · have : G.neighborFinset t ∩ G.neighborFinset v = ∅ := by
              rw [Finset.eq_empty_iff_forall_not_mem]
              intro x hx
              rw [Finset.mem_inter] at hx
              apply neighborSet_indep_of_triangleFree h_tri v
              · exact hx.2
              · exact ht
              · exact G.ne_of_adj hx.1
              · exact hx.1
            rw [this, Finset.card_empty, zero_add]
            have : G.neighborFinset t ∩ {v} = {v} := by
              rw [Finset.inter_singleton_of_mem]
              rw [mem_neighborFinset]
              exact G.adj_symm ht
            rw [this, Finset.card_singleton]
          · rw [Finset.disjoint_iff_inter_eq_empty]
            rw [Finset.inter_distrib_left]
            have : G.neighborFinset t ∩ G.neighborFinset v = ∅ := by
              rw [Finset.eq_empty_iff_forall_not_mem]
              intro x hx
              rw [Finset.mem_inter] at hx
              apply neighborSet_indep_of_triangleFree h_tri v
              · exact hx.2
              · exact ht
              · exact G.ne_of_adj hx.1
              · exact hx.1
            rw [this, Finset.empty_inter]
        rw [card_inter] at h_t_deg
        linarith

      obtain ⟨h1, h2, h3, h_distinct, h_subset⟩ : ∃ h1 h2 h3, h1 ≠ h2 ∧ h1 ≠ h3 ∧ h2 ≠ h3 ∧ {h1, h2, h3} ⊆ N_t_V' := by
        -- Use card >= 3
        rcases Finset.card_ge_three.1 h_Nt_V'_card with ⟨x, y, z, hxy, hyz, hxz, hx, hy, hz⟩
        use x, y, z
        exact ⟨hxy, hxz, hyz, by
          simp only [Finset.insert_subset, Finset.singleton_subset_iff]
          exact ⟨hx, hy, hz⟩⟩

      -- Construct the 6-independent set
      let S6 := {h1, h2, h3} ∪ (N0.erase t)
      
      have hS6_indep : G.IsIndepSet S6 := by
        sorry

      have hS6_card : S6.card = 6 := by
        sorry

      exact h_no6 _ ⟨hS6_card, hS6_indep⟩

    omega

  intro v
  exact le_antisymm (h_le v) (h_ge v)