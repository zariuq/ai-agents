/-
# D-Separation in Bayesian Networks

D-separation is the graphical criterion for conditional independence in
Bayesian networks. Two sets of variables X and Y are conditionally independent
given Z if and only if they are d-separated by Z in the graph.

## Overview

A path from X to Y is **blocked** by Z if:
1. The path contains a **chain** (A → B → C) or **fork** (A ← B → C) where B ∈ Z
2. The path contains a **collider** (A → B ← C) where neither B nor any
   descendant of B is in Z

X and Y are **d-separated** by Z if every undirected path from X to Y is blocked.

## Key Results

- `DSeparated`: Definition of d-separation
- `dsep_symmetric`: D-separation is symmetric in X and Y
- `dsep_implies_cond_indep`: D-separation implies conditional independence
  (the soundness theorem - this requires measure theory and is stated as a
  specification for now)

## References

- Pearl, "Probabilistic Reasoning in Intelligent Systems" (1988), Chapter 3
- Koller & Friedman, "Probabilistic Graphical Models" (2009), Chapter 3
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph

namespace Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation

open DirectedGraph

variable {V : Type*}

/-! ## Undirected Edges and Paths

For d-separation, we consider undirected paths (ignoring edge direction)
but track the local structure (chain, fork, collider) at each node.
-/

/-- An undirected edge: either u → v or v → u in the directed graph. -/
def UndirectedEdge (G : DirectedGraph V) (u v : V) : Prop :=
  G.edges u v ∨ G.edges v u

/-- Undirected edge is symmetric. -/
theorem undirectedEdge_symm (G : DirectedGraph V) (u v : V) :
    UndirectedEdge G u v ↔ UndirectedEdge G v u := by
  unfold UndirectedEdge
  exact or_comm

/-! ## Path Triples and Colliders

A path triple (a, b, c) represents three consecutive vertices on an undirected path.
The structure at b determines whether the path is blocked.
-/

/-- A path triple (a, b, c) where consecutive vertices are connected. -/
structure PathTriple (G : DirectedGraph V) where
  a : V
  b : V
  c : V
  edge_ab : UndirectedEdge G a b
  edge_bc : UndirectedEdge G b c
  a_ne_c : a ≠ c

/-- A collider at b: both edges point INTO b (a → b ← c). -/
def IsCollider (G : DirectedGraph V) (t : PathTriple G) : Prop :=
  G.edges t.a t.b ∧ G.edges t.c t.b

/-- A non-collider at b: at least one edge points OUT of b.
    This includes chains (a → b → c) and forks (a ← b → c). -/
def IsNonCollider (G : DirectedGraph V) (t : PathTriple G) : Prop :=
  ¬IsCollider G t

/-- At a non-collider, the middle vertex has at least one outgoing edge. -/
theorem nonCollider_has_outgoing (G : DirectedGraph V) (t : PathTriple G)
    (h : IsNonCollider G t) : G.edges t.b t.a ∨ G.edges t.b t.c := by
  unfold IsNonCollider IsCollider at h
  push_neg at h
  -- We have: G.edges t.a t.b → ¬G.edges t.c t.b
  cases t.edge_ab with
  | inl hab => -- a → b
    have hnot_cb := h hab
    -- Since edge_bc is undirected: b → c or c → b
    -- ¬(c → b) so must be b → c
    cases t.edge_bc with
    | inl hbc => right; exact hbc
    | inr hcb => exact absurd hcb hnot_cb
  | inr hba => -- b → a
    left; exact hba

/-! ## Blocking Conditions

A path through a node b is blocked by conditioning set Z if:
- b is a NON-collider and b ∈ Z (blocking by conditioning)
- b is a COLLIDER and neither b nor any descendant of b is in Z (blocking by non-conditioning)
-/

/-- A path triple is blocked at the middle vertex by conditioning set Z. -/
def IsBlocked (G : DirectedGraph V) (Z : Set V) (t : PathTriple G) : Prop :=
  (IsNonCollider G t ∧ t.b ∈ Z) ∨
  (IsCollider G t ∧ t.b ∉ Z ∧ ∀ d ∈ G.descendants t.b, d ∉ Z)

/-- A path triple is active (not blocked) given conditioning set Z. -/
def IsActive (G : DirectedGraph V) (Z : Set V) (t : PathTriple G) : Prop :=
  ¬IsBlocked G Z t

/-- Active non-collider: not in Z. -/
theorem active_nonCollider_not_in_Z (G : DirectedGraph V) (Z : Set V)
    (t : PathTriple G) (hact : IsActive G Z t) (hnonc : IsNonCollider G t) :
    t.b ∉ Z := by
  unfold IsActive IsBlocked at hact
  push_neg at hact
  exact hact.1 hnonc

/-- Active collider: b or a descendant is in Z. -/
theorem active_collider_desc_in_Z (G : DirectedGraph V) (Z : Set V)
    (t : PathTriple G) (hact : IsActive G Z t) (hcol : IsCollider G t) :
    t.b ∈ Z ∨ ∃ d ∈ G.descendants t.b, d ∈ Z := by
  unfold IsActive IsBlocked at hact
  push_neg at hact
  -- hact.2 hcol : t.b ∉ Z → ∃ d ∈ G.descendants t.b, d ∈ Z
  -- Convert implication to disjunction
  by_cases hbZ : t.b ∈ Z
  · left; exact hbZ
  · right; exact hact.2 hcol hbZ

/-! ## D-Separation (Simplified Definition)

We define d-separation using a predicate on paths. A full formalization
would use an inductive path type; here we use a simplified approach.
-/

/-- Predicate: There exists an active (unblocked) path from x to y given Z.
    This is defined as the negation of "all paths are blocked". -/
def HasActivePath (G : DirectedGraph V) (Z : Set V) (x y : V) : Prop :=
  -- Simplified: x and y are connected by an undirected edge and either:
  -- (1) x = y (trivial path), or
  -- (2) There's a direct undirected edge x ~ y (no intermediate vertex to block), or
  -- (3) There's a longer path with at least one unblocked triple
  x = y ∨
  (UndirectedEdge G x y ∧ x ≠ y) ∨
  (∃ b : V, b ≠ x ∧ b ≠ y ∧
    UndirectedEdge G x b ∧ UndirectedEdge G b y ∧
    ∃ (hab : UndirectedEdge G x b) (hbc : UndirectedEdge G b y) (hac : x ≠ y),
      IsActive G Z ⟨x, b, y, hab, hbc, hac⟩)

/-- D-separation: X and Y are d-separated by Z if no active paths exist. -/
def DSeparated (G : DirectedGraph V) (X Y Z : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≠ y → ¬HasActivePath G Z x y

/-! ## D-Separation (Full Trail-Based Definition)

The placeholder `HasActivePath` above only inspects very short paths.
The definitions in this section are the proper arbitrary-length notion:

- `IsTrail` tracks undirected adjacency along a vertex list.
- `HasActiveTrail` packages endpoints + trail + activation.
- `DSeparatedFull` quantifies over all endpoints in X,Y.
-/

/-- A vertex list is an undirected trail if each consecutive pair is adjacent. -/
inductive IsTrail (G : DirectedGraph V) : List V → Prop
  | single (v : V) : IsTrail G [v]
  | cons {u v : V} {rest : List V}
      (hEdge : UndirectedEdge G u v)
      (hTail : IsTrail G (v :: rest)) :
      IsTrail G (u :: v :: rest)

/--
`ActiveTrail G Z p` is the proof-relevant trail predicate:
each extension step carries an undirected edge witness, and each internal node
carries a proof that the corresponding triple is active.
-/
inductive ActiveTrail (G : DirectedGraph V) (Z : Set V) : List V → Prop
  | single (v : V) : ActiveTrail G Z [v]
  | two {u v : V} (hEdge : UndirectedEdge G u v) : ActiveTrail G Z [u, v]
  | cons {a b c : V} {rest : List V}
      (hab : UndirectedEdge G a b)
      (hbc : UndirectedEdge G b c)
      (hac : a ≠ c)
      (hAct : IsActive G Z ⟨a, b, c, hab, hbc, hac⟩)
      (hTail : ActiveTrail G Z (b :: c :: rest)) :
      ActiveTrail G Z (a :: b :: c :: rest)

/-- Endpoints of a non-empty path list. -/
def PathEndpoints : List V → Option (V × V)
  | [] => none
  | [v] => some (v, v)
  | v :: rest =>
      match rest with
      | [] => some (v, v)
      | h :: t => some (v, (h :: t).getLast (by simp))

/-- Existence of an arbitrary-length active trail from `x` to `y` given `Z`. -/
def HasActiveTrail (G : DirectedGraph V) (Z : Set V) (x y : V) : Prop :=
  ∃ p : List V, p ≠ [] ∧
    PathEndpoints p = some (x, y) ∧
    ActiveTrail G Z p

/-- Full d-separation: no active trails between X and Y given Z. -/
def DSeparatedFull (G : DirectedGraph V) (X Y Z : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≠ y → ¬HasActiveTrail G Z x y

/-- Any legacy short active path is a full active trail. -/
theorem hasActiveTrail_of_hasActivePath
    (G : DirectedGraph V) (Z : Set V) (x y : V) :
    HasActivePath G Z x y → HasActiveTrail G Z x y := by
  intro h
  unfold HasActivePath at h
  rcases h with rfl | ⟨hedge, _hne⟩ | ⟨b, hbx, hby, hxb, hby', hab, hbc, hxy, hAct⟩
  · refine ⟨[x], by simp, ?_, ActiveTrail.single x⟩
    simp [PathEndpoints]
  · refine ⟨[x, y], by simp, ?_, ActiveTrail.two hedge⟩
    simp [PathEndpoints]
  · refine ⟨[x, b, y], by simp, ?_, ?_⟩
    · simp [PathEndpoints]
    · exact ActiveTrail.cons hab hbc hxy hAct (ActiveTrail.two hby')

/-- Full d-separation implies legacy d-separation. -/
theorem dsep_of_dsepFull (G : DirectedGraph V) (X Y Z : Set V) :
    DSeparatedFull G X Y Z → DSeparated G X Y Z := by
  intro hfull x hx y hy hxy hshort
  exact hfull x hx y hy hxy (hasActiveTrail_of_hasActivePath G Z x y hshort)

/-! ## Moralized-Ancestral Graph (bridge scaffolding)

This section provides the graph objects used by the standard d-separation
equivalence proof:

1. Restrict to ancestors of `X ∪ Y ∪ Z`.
2. Moralize (drop direction + connect co-parents).
3. Reduce d-separation to ordinary graph separation in the moralized graph.
-/

/-- Ancestor closure of a vertex set. -/
def ancestorClosure (G : DirectedGraph V) (S : Set V) : Set V :=
  {v | v ∈ S ∨ ∃ s ∈ S, G.Reachable v s}

/-- Directed induced subgraph on a vertex set `W`. -/
def inducedSubgraph (G : DirectedGraph V) (W : Set V) : DirectedGraph V where
  edges u v := W u ∧ W v ∧ G.edges u v

/-- Moralized undirected edge relation for a DAG (on a fixed vertex universe). -/
def moralUndirectedEdge (G : DirectedGraph V) (u v : V) : Prop :=
  UndirectedEdge G u v ∨ ∃ c : V, G.edges u c ∧ G.edges v c

/-- Moralized graph represented as a symmetric directed graph. -/
def moralGraph (G : DirectedGraph V) : DirectedGraph V where
  edges u v := moralUndirectedEdge G u v

/-- A path avoids `Z` internally if all interior vertices are outside `Z`. -/
def PathAvoidsInternals (Z : Set V) : List V → Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | _ :: b :: rest => b ∉ Z ∧ PathAvoidsInternals Z (b :: rest)

/-- Separation in the moralized graph (scaffold definition). -/
def SeparatedInMoral (G : DirectedGraph V) (X Y Z : Set V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, x ≠ y →
    ¬∃ p : List V, p ≠ [] ∧ PathEndpoints p = some (x, y) ∧
      IsTrail (moralGraph G) p ∧ PathAvoidsInternals Z p

theorem moralUndirectedEdge_symm (G : DirectedGraph V) (u v : V) :
    moralUndirectedEdge G u v ↔ moralUndirectedEdge G v u := by
  constructor <;> intro h
  · rcases h with huv | ⟨c, huc, hvc⟩
    · left
      exact (undirectedEdge_symm G u v).1 huv
    · right
      exact ⟨c, hvc, huc⟩
  · rcases h with huv | ⟨c, hvc, huc⟩
    · left
      exact (undirectedEdge_symm G v u).1 huv
    · right
      exact ⟨c, huc, hvc⟩

theorem ancestorClosure_mono (G : DirectedGraph V) {S T : Set V}
    (hST : S ⊆ T) : ancestorClosure G S ⊆ ancestorClosure G T := by
  intro v hv
  rcases hv with hs | ⟨s, hs, hreach⟩
  · exact Or.inl (hST hs)
  · exact Or.inr ⟨s, hST hs, hreach⟩

theorem inducedSubgraph_edge_of_edge (G : DirectedGraph V) (W : Set V) {u v : V}
    (hu : W u) (hv : W v) (h : G.edges u v) :
    (inducedSubgraph G W).edges u v := by
  exact ⟨hu, hv, h⟩

/-! ## Basic Properties of D-Separation -/

/-- Empty X means trivial d-separation. -/
theorem dsep_of_empty_X (G : DirectedGraph V) (Y Z : Set V) :
    DSeparated G ∅ Y Z := by
  intro x hx _ _ _
  exact absurd hx (Set.notMem_empty x)

/-- Empty Y means trivial d-separation. -/
theorem dsep_of_empty_Y (G : DirectedGraph V) (X Z : Set V) :
    DSeparated G X ∅ Z := by
  intro _ _ y hy _
  exact absurd hy (Set.notMem_empty y)

/-- Collider is symmetric: swapping endpoints preserves collider status. -/
theorem isCollider_comm (a b c : V) (hab : UndirectedEdge G a b) (hbc : UndirectedEdge G b c)
    (hac : a ≠ c) (hcb : UndirectedEdge G c b) (hba : UndirectedEdge G b a) (hca : c ≠ a) :
    IsCollider G ⟨a, b, c, hab, hbc, hac⟩ ↔ IsCollider G ⟨c, b, a, hcb, hba, hca⟩ := by
  unfold IsCollider
  exact and_comm

/-- D-separation is symmetric in X and Y (statement).
    The proof requires careful handling of path reversal. -/
theorem dsep_symmetric (G : DirectedGraph V) (X Y Z : Set V)
    (hdsep : DSeparated G X Y Z) : DSeparated G Y X Z := by
  intro y hy x hx hne hpath
  -- We need to show ¬HasActivePath G Z y x
  -- Given: ∀ paths from x ∈ X to y ∈ Y are blocked
  -- Transform path from y to x into path from x to y
  apply hdsep x hx y hy hne.symm
  unfold HasActivePath at hpath ⊢
  rcases hpath with rfl | ⟨hedge, hne'⟩ | ⟨b, hby, hbx, hyb, hbx', hab', hbc', hac', hactive⟩
  · left; rfl
  · right; left
    exact ⟨(undirectedEdge_symm G y x).mp hedge, hne'.symm⟩
  · -- Path y ~ b ~ x becomes x ~ b ~ y
    right; right
    use b, hbx, hby
    have hxb := (undirectedEdge_symm G b x).mp hbx'
    have hby'' := (undirectedEdge_symm G y b).mp hyb
    refine ⟨hxb, hby'', hxb, hby'', hne.symm, ?_⟩
    -- Active triple ⟨y, b, x⟩ → Active triple ⟨x, b, y⟩
    -- The key: collider status only depends on edge directions into b
    -- IsCollider ⟨y,b,x⟩ = (y→b ∧ x→b) = IsCollider ⟨x,b,y⟩
    unfold IsActive at hactive ⊢
    intro hblocked
    apply hactive
    unfold IsBlocked at hblocked ⊢
    rcases hblocked with ⟨hnc_xby, hbZ⟩ | ⟨hc_xby, hnotZ, hdesc⟩
    · -- ⟨x,b,y⟩ is non-collider, b ∈ Z
      left
      refine ⟨?_, hbZ⟩
      unfold IsNonCollider at hnc_xby ⊢
      unfold IsCollider at hnc_xby ⊢
      -- ¬(G.edges x b ∧ G.edges y b) ↔ ¬(G.edges y b ∧ G.edges x b)
      rw [and_comm] at hnc_xby
      exact hnc_xby
    · -- ⟨x,b,y⟩ is collider, b ∉ Z, no desc in Z
      right
      refine ⟨?_, hnotZ, hdesc⟩
      unfold IsCollider at hc_xby ⊢
      exact ⟨hc_xby.2, hc_xby.1⟩

/-! ## Soundness Theorem (Specification)

The key theorem: d-separation implies conditional independence.
This requires:
1. A probability measure on the joint space
2. The measure satisfies the factorization property
3. Conditional independence from Mathlib

For now, we state this as a class/specification.
-/

/-!
Note: The proper definition of conditional independence for vertex sets is
`CondIndepVertices` in DSeparationSoundness.lean, which uses Mathlib's
measure-theoretic `CondIndep`. That definition requires:
- A `BayesianNetwork V` (not just a graph)
- A probability measure `μ` on the joint space
- `[StandardBorelSpace]` instances for state spaces

The d-separation soundness theorem (d-sep ⟹ conditional independence) requires
additionally that the measure satisfies the local Markov property. This is a
major theorem (Koller & Friedman Thm 3.3) that we do not yet have.
-/

/-! ## Special Cases -/

/-- Single vertex d-separation: {v} ⊥ Y | Z when v has no active path to Y. -/
theorem dsep_singleton (G : DirectedGraph V) (v : V) (Y Z : Set V)
    (h : ∀ y ∈ Y, v ≠ y → ¬HasActivePath G Z v y) : DSeparated G {v} Y Z := by
  intro x hx y hy hne
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact h y hy hne

/-- If no direct edges exist between X and Y, there's no direct active path. -/
theorem dsep_no_direct_edges (G : DirectedGraph V) (X Y : Set V)
    (hsep : ∀ x ∈ X, ∀ y ∈ Y, ¬UndirectedEdge G x y) :
    ∀ x ∈ X, ∀ y ∈ Y, x ≠ y → ¬(x = y ∨ (UndirectedEdge G x y ∧ x ≠ y)) := by
  intro x hx y hy hne hpath
  rcases hpath with rfl | ⟨hedge, _⟩
  · exact hne rfl
  · exact hsep x hx y hy hedge

/-! ## Summary

This file establishes:

1. **Undirected edges**: Ignoring direction for path analysis
2. **Path triples**: Local structure (collider vs non-collider) at each node
3. **Blocking conditions**: When a conditioning set blocks a path
4. **D-separation**: All paths blocked ⟹ X ⊥ Y | Z
5. **Basic properties**: Empty sets, symmetry
6. **Soundness specification**: D-sep implies conditional independence (placeholder)

The full treatment requires:
- Inductive path types for arbitrary length paths
- Connection to BayesianNetwork factorization
- Mathlib's conditional independence API
-/

end Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
