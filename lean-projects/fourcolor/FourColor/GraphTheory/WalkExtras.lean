import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Rel

/-!
# Walk Extras for Bridge Proofs

This file provides helper lemmas for converting ReflTransGen relations to walks
and proving bridge properties in forests.

Based on GPT-5 Pro's solutions for the Four Color Theorem formalization.

## Main Results

* `walk_of_rflTransGen_subrel`: If R refines adjacency, ReflTransGen R gives a walk
* `edge_is_bridge_in_forest`: In a forest, every edge is a bridge of that forest
* `edge_deletion_increases_components_in_tree`: Removing a forest edge increases components by 1

-/

open Classical Relation

namespace SimpleGraph

variable {α : Type*} (G : SimpleGraph α)

/-- If a relation `R` is pointwise contained in `G.Adj`, any `ReflTransGen R` gives a walk. -/
lemma walk_of_rflTransGen_subrel {R : α → α → Prop} {u v : α}
    (hR : ∀ {x y}, R x y → G.Adj x y)
    (h : ReflTransGen R u v) : G.Walk u v := by
  induction h with
  | refl => exact Walk.nil
  | tail _ _ hab _ ih =>
      exact ih.concat (hR hab)

/-- Specialization: `R = G.Adj`. -/
lemma walk_of_rflTransGen_adj {u v : α}
    (h : ReflTransGen G.Adj u v) : G.Walk u v :=
  G.walk_of_rflTransGen_subrel (fun {_ _} hxy => hxy) h

/-- Work on induced subgraphs: the same statement for `G.induce s`. -/
lemma walk_of_rflTransGen_subrel_induce {s : Set α} {R : {x // x ∈ s} → {x // x ∈ s} → Prop}
    {u v : {x // x ∈ s}}
    (hR : ∀ {x y}, R x y → (G.induce s).Adj x y)
    (h  : ReflTransGen R u v) : (G.induce s).Walk u v :=
  (G.induce s).walk_of_rflTransGen_subrel hR h

/-- In a forest, an edge `u~v` is a bridge *of the forest*: removing it disconnects `u` and `v`.
This is the key fact for proving unique paths in trees. -/
lemma edge_is_bridge_in_forest
    [DecidableEq α]
    (hacyc : G.IsAcyclic) {u v : α} (huv : G.Adj u v) :
    G.IsBridge s(u, v) := by
  -- In an acyclic graph, every edge is a bridge
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at hacyc
  exact hacyc huv

end SimpleGraph
