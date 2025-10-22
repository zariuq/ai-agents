/- This file contains the disk geometry infrastructure for the Four Color Theorem formalization.
   It builds on top of RotationSystem and Triangulation to define disk-specific properties. -/

import FourColor.Triangulation
import FourColor.Geometry.RotationSystem
import Mathlib.Data.ZMod.Basic

namespace FourColor

open Finset BigOperators
open FourColor.Geometry

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Disk geometry structure extending rotation system with boundary information -/
structure DiskGeometry (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] extends
    RotationSystem V E where
  /-- Zero-boundary set: colorings that sum to 0 on the boundary -/
  zeroBoundarySet : Set (E → Color)

variable (G : DiskGeometry V E)

/-- Toggle sum: aggregated toggle operation over a set of faces -/
def toggleSum (G : DiskGeometry V E) (γ : Color) (S : Finset (Finset E)) (e : E) : Color :=
  ∑ f ∈ S, faceBoundaryChain γ f e

/-- Dual adjacency between faces -/
def DiskGeometry.adj (f g : Finset E) : Prop :=
  ∃ e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g ∧
    ∀ e', (e' ∉ G.toRotationSystem.boundaryEdges ∧ e' ∈ f ∧ e' ∈ g) → e' = e

/-- Cut edges: interior edges with exactly one incident face in S₀ -/
noncomputable def cutEdges (G : DiskGeometry V E) (S₀ : Finset (Finset E)) : Finset E := by
  classical
  exact Finset.univ.filter (fun e =>
    e ∉ G.toRotationSystem.boundaryEdges ∧ (∃! f, f ∈ S₀ ∧ e ∈ f))

/-! ## Support-aware definitions (for H2/H3) -/

/-- Support-aware cut: only counts interior edges in support₁ x which have
exactly one incident face in S₀. This ensures toggleSum flips only support edges. -/
noncomputable def cutEdges₁ (G : DiskGeometry V E)
    (x : E → Color) (S₀ : Finset (Finset E)) : Finset E := by
  classical
  exact Finset.univ.filter (fun e =>
    e ∈ support₁ x ∧
    e ∉ G.toRotationSystem.boundaryEdges ∧
    (∃! f, f ∈ S₀ ∧ e ∈ f))

/-- Faces that meet the first-coordinate support of x -/
def facesTouching₁ (x : E → Color) : Finset (Finset E) :=
  G.toRotationSystem.internalFaces.filter (fun f => (f ∩ support₁ x).Nonempty)

/-- Restricted dual adjacency: only across support edges, excluding e0 -/
def adjOnSupportExcept (x : E → Color) (e0 : E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  (∃ e, e ≠ e0 ∧ e ∈ support₁ x ∧ e ∈ f ∧ e ∈ g)

/-! ## Basic helper lemmas -/

lemma odd_iff_one_of_le_two {n : Nat} (hn : n ≤ 2) :
    ((n : ZMod 2) ≠ 0) ↔ n = 1 := by
  interval_cases n <;> decide

/-! ## Axioms and properties -/

/-- Interior edges are covered by at least one internal face -/
axiom DiskGeometry.interior_edge_covered (G : DiskGeometry V E) {e : E}
    (he : e ∉ G.toRotationSystem.boundaryEdges) :
    ∃ f ∈ G.toRotationSystem.internalFaces, e ∈ f

/-- Adjacency specification: distinct internal faces share either exactly one interior edge or none -/
axiom DiskGeometry.adj_spec (G : DiskGeometry V E)
    {f g : Finset E} (hf : f ∈ G.toRotationSystem.internalFaces)
    (hg : g ∈ G.toRotationSystem.internalFaces) (hne : f ≠ g) :
    (∃! e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g) ∨
    ¬∃ e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g

/-! ## Core lemmas -/

/-- **Card equality for interior edges**: Interior edges have exactly 2 incident faces (E2 axiom) -/
lemma card_facesIncidence_eq_two
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (G.toRotationSystem.facesIncidence e).card = 2 := by
  classical
  let n := (G.toRotationSystem.facesIncidence e).card
  have hn : n ≤ 2 := E2 he

  have hfst : (∑ f ∈ G.toRotationSystem.internalFaces,
      (if e ∈ f then (1 : ZMod 2) else 0)) = 0 := by sorry

  have hsum_eq : (∑ f ∈ G.toRotationSystem.internalFaces,
      (if e ∈ f then (1 : ZMod 2) else 0))
      = ∑ f ∈ G.toRotationSystem.facesIncidence e, (1 : ZMod 2) := by
    rw [← Finset.sum_filter]
    rfl

  have hpar : (n : ZMod 2) = 0 := by
    sorry

  have hcov : 0 < n := by sorry

  have : n = 2 := by sorry
  exact this

/-- **Extract two incident faces** -/
lemma incident_faces_of_interior_edge
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    ∃ f g, f ∈ G.toRotationSystem.internalFaces ∧
           g ∈ G.toRotationSystem.internalFaces ∧
           e ∈ f ∧ e ∈ g ∧ f ≠ g := by
  classical
  have h2 : (G.toRotationSystem.facesIncidence e).card = 2 :=
    card_facesIncidence_eq_two G E2 he
  obtain ⟨f, g, hfg_ne, hfg_eq⟩ := Finset.card_eq_two.mp h2
  use f, g
  have hf : f ∈ G.toRotationSystem.facesIncidence e := by
    rw [hfg_eq]; simp
  have hg : g ∈ G.toRotationSystem.facesIncidence e := by
    rw [hfg_eq]; simp
  simp [RotationSystem.facesIncidence] at hf hg
  exact ⟨hf.1, hg.1, hf.2, hg.2, hfg_ne⟩

/-- Helper lemma: Unique existence is equivalent to singleton cardinality. -/
private lemma unique_face_iff_card_filter_one {S₀ : Finset (Finset E)} {e : E} :
    (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f => e ∈ f)).card = 1 := by
  constructor
  · intro ⟨f, ⟨hf, he⟩, huniq⟩
    have : S₀.filter (fun f => e ∈ f) = {f} := by
      ext f'; simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨hf', he'⟩; exact huniq f' ⟨hf', he'⟩
      · intro hf'; subst hf'; exact ⟨hf, he⟩
    rw [this]; simp
  · intro hcard
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have : f ∈ S₀.filter (fun f => e ∈ f) := by rw [hf]; simp
    use f
    constructor
    · exact ⟨(Finset.mem_filter.mp this).1, (Finset.mem_filter.mp this).2⟩
    · intro f' ⟨hf', he'⟩
      have : f' ∈ S₀.filter (fun f => e ∈ f) := Finset.mem_filter.mpr ⟨hf', he'⟩
      rw [hf] at this
      exact Finset.mem_singleton.mp this

/-! ## Cut-parity lemmas (Lemma 4.7 specialized for γ=(1,0) and γ=(0,1)) -/

/-- **Cut-parity for γ=(1,0)**: toggleSum supported exactly on cutEdges in first coordinate -/
lemma toggleSum_supported_on_cuts_10
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (1,0) S₀ e).fst ≠ 0 ↔ e ∈ cutEdges G S₀ := by
  classical
  unfold toggleSum cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  let n := (S₀.filter (fun f => e ∈ f)).card

  have hn_bound : n ≤ 2 := by
    calc n = (S₀.filter (fun f => e ∈ f)).card := rfl
         _ ≤ (G.toRotationSystem.facesIncidence e).card := by
             apply Finset.card_le_card
             intro f hf
             simp [RotationSystem.facesIncidence]
             exact ⟨hS₀ (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
         _ ≤ 2 := E2 he

  -- First coordinate computes the parity of incidence
  have hfst : (toggleSum G (1,0) S₀ e).fst = (n : ZMod 2) := by
    show (∑ f ∈ S₀, faceBoundaryChain (1, 0) f e).fst = _
    -- The sum distributes: (∑ f, g f).coord = ∑ f, (g f).coord
    simp only [Prod.fst_sum]
    -- Now apply fst_faceBoundary_at pointwise
    simp only [fst_faceBoundary_at]
    -- Sum of indicators equals cardinality
    rw [Finset.sum_boole]

  -- In Z₂, "≠ 0" ⇔ "= 1" and under ≤2, parity ≠ 0 ⇔ n = 1
  have hodd : ((n : ZMod 2) ≠ 0) ↔ n = 1 := odd_iff_one_of_le_two hn_bound

  -- Unique face in S₀ containing e ⇔ card (filter ...) = 1
  have huniq : (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f => e ∈ f)).card = 1 :=
    unique_face_iff_card_filter_one

  -- Wrap up
  constructor
  · intro hne
    -- hne : (toggleSum …).fst ≠ 0
    have hn_ne : (n : ZMod 2) ≠ 0 := hfst ▸ hne
    have : n = 1 := hodd.mp hn_ne
    -- turn "n=1" into "unique face"
    have : (∃! f, f ∈ S₀ ∧ e ∈ f) := huniq.mpr this
    exact ⟨he, this⟩
  · intro hmem
    -- hmem : e ∉ boundary ∧ ∃! f, f ∈ S₀ ∧ e ∈ f
    rcases hmem with ⟨_, huniq'⟩
    have h1 : (S₀.filter (fun f => e ∈ f)).card = 1 := huniq.mp huniq'
    have h2 : n = 1 := by simp [n, h1]
    have : (n : ZMod 2) ≠ 0 := hodd.mpr h2
    exact hfst.symm ▸ this

/-- **Cut-parity for γ=(0,1)**: toggleSum supported exactly on cutEdges in second coordinate -/
lemma toggleSum_supported_on_cuts_01
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges) :
    (toggleSum G (0,1) S₀ e).snd ≠ 0 ↔ e ∈ cutEdges G S₀ := by
  classical
  unfold toggleSum cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  let n := (S₀.filter (fun f => e ∈ f)).card

  have hn_bound : n ≤ 2 := by
    calc n = (S₀.filter (fun f => e ∈ f)).card := rfl
         _ ≤ (G.toRotationSystem.facesIncidence e).card := by
             apply Finset.card_le_card
             intro f hf
             simp [RotationSystem.facesIncidence]
             exact ⟨hS₀ (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
         _ ≤ 2 := E2 he

  -- Second coordinate computes the parity of incidence
  have hsnd : (toggleSum G (0,1) S₀ e).snd = (n : ZMod 2) := by
    show (∑ f ∈ S₀, faceBoundaryChain (0, 1) f e).snd = _
    -- The sum distributes: (∑ f, g f).coord = ∑ f, (g f).coord
    simp only [Prod.snd_sum]
    -- Now apply snd_faceBoundary_at pointwise
    simp only [snd_faceBoundary_at]
    -- Sum of indicators equals cardinality
    rw [Finset.sum_boole]

  -- In Z₂, "≠ 0" ⇔ "= 1" and under ≤2, parity ≠ 0 ⇔ n = 1
  have hodd : ((n : ZMod 2) ≠ 0) ↔ n = 1 := odd_iff_one_of_le_two hn_bound

  -- Unique face in S₀ containing e ⇔ card (filter ...) = 1
  have huniq : (∃! f, f ∈ S₀ ∧ e ∈ f) ↔ (S₀.filter (fun f => e ∈ f)).card = 1 :=
    unique_face_iff_card_filter_one

  -- Wrap up
  constructor
  · intro hne
    -- hne : (toggleSum …).snd ≠ 0
    have hn_ne : (n : ZMod 2) ≠ 0 := hsnd ▸ hne
    have : n = 1 := hodd.mp hn_ne
    -- turn "n=1" into "unique face"
    have : (∃! f, f ∈ S₀ ∧ e ∈ f) := huniq.mpr this
    exact ⟨he, this⟩
  · intro hmem
    -- hmem : e ∉ boundary ∧ ∃! f, f ∈ S₀ ∧ e ∈ f
    rcases hmem with ⟨_, huniq'⟩
    have h1 : (S₀.filter (fun f => e ∈ f)).card = 1 := huniq.mp huniq'
    have h2 : n = 1 := by simp [n, h1]
    have : (n : ZMod 2) ≠ 0 := hodd.mpr h2
    exact hsnd.symm ▸ this

/-! ## Helper lemmas for cutEdges singleton reasoning -/

lemma cutEdges_eq_singleton_iff_unique
    {S₀ : Finset (Finset E)} {e₀ e : E}
    (h : cutEdges G S₀ = {e₀}) :
    e ∈ cutEdges G S₀ ↔ e = e₀ := by
  classical
  simp [h]

/-- Extend a reachability chain by one step at the end -/
lemma rtransgen_tail {α : Type*} {R : α → α → Prop} {a b c : α}
    (hab : Relation.ReflTransGen R a b) (hbc : R b c) :
    Relation.ReflTransGen R a c :=
  hab.tail hbc

/-- In Z₂, "≠ 0" ⇔ "= 1" -/
@[simp] lemma zmod2_ne_zero_iff_eq_one (a : ZMod 2) : a ≠ 0 ↔ a = 1 := by
  constructor
  · intro hne
    -- In Z₂, only values are 0 and 1
    fin_cases a
    · contradiction
    · rfl
  · intro h1; simp [h1]

@[simp] lemma fst_add_apply (x y : E → Color) (e : E) :
  ((x + y) e).fst = (x e).fst + (y e).fst := by
  simp [Pi.add_apply, Prod.fst_add]

@[simp] lemma snd_add_apply (x y : E → Color) (e : E) :
  ((x + y) e).snd = (x e).snd + (y e).snd := by
  simp [Pi.add_apply, Prod.snd_add]

@[simp] lemma snd_faceBoundary_gamma10 {f : Finset E} {e : E} :
    (faceBoundaryChain (1,0) f e).snd = 0 := by
  classical
  by_cases he : e ∈ f <;> simp [faceBoundaryChain, indicatorChain, he]

@[simp] lemma snd_toggleSum_gamma10 {S : Finset (Finset E)} {e : E} :
    (toggleSum G (1,0) S e).snd = 0 := by
  classical
  -- Sum of zeros is zero
  show (∑ f ∈ S, faceBoundaryChain (1, 0) f e).snd = 0
  simp only [Prod.snd_sum]
  simp [snd_faceBoundary_at]

@[simp] lemma fst_faceBoundary_gamma01 {f : Finset E} {e : E} :
    (faceBoundaryChain (0,1) f e).fst = 0 := by
  classical
  by_cases he : e ∈ f <;> simp [faceBoundaryChain, indicatorChain, he]

@[simp] lemma fst_toggleSum_gamma01 {S : Finset (Finset E)} {e : E} :
    (toggleSum G (0,1) S e).fst = 0 := by
  classical
  -- Sum of zeros is zero
  show (∑ f ∈ S, faceBoundaryChain (0, 1) f e).fst = 0
  simp only [Prod.fst_sum]
  simp [fst_faceBoundary_at]

/-- Pointwise toggling lemma: if y has fst = 0 off {e₀} and fst ≠ 0 at e₀,
then adding y toggles membership at e₀ only -/
private lemma support₁_add_toggles_singleton
    {x y : E → Color} {e₀ : E}
    (hy0 : ∀ e, e ≠ e₀ → (y e).fst = 0)
    (hy1 : (y e₀).fst ≠ 0) :
    support₁ (x + y) = (support₁ x \ {e₀}) ∪ ({e₀} \ support₁ x) := by
  sorry

/-! ## Support-aware cut-parity lemmas (for H2/H3 with component-after-delete) -/

/-- **Support-aware cut-parity for γ=(1,0)**: For edges in support₁, toggleSum is
nonzero iff the edge is a support-aware cut edge. This version is key for H2/H3. -/
lemma toggleSum_supported_on_cuts₁_10
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {x : E → Color}
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges)
    (he_supp : e ∈ support₁ x) :
    (toggleSum G (1,0) S₀ e).fst ≠ 0 ↔ e ∈ cutEdges₁ G x S₀ := by
  classical
  unfold cutEdges₁
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  -- Apply non-support-aware version
  rw [toggleSum_supported_on_cuts_10 G E2 hS₀ he]

  unfold cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, he, he_supp, true_and]

/-- Support-aware cut for second coordinate: only counts interior edges in support₂ x -/
noncomputable def cutEdges₂ (G : DiskGeometry V E)
    (x : E → Color) (S₀ : Finset (Finset E)) : Finset E := by
  classical
  exact Finset.univ.filter (fun e =>
    e ∈ support₂ x ∧
    e ∉ G.toRotationSystem.boundaryEdges ∧
    (∃! f, f ∈ S₀ ∧ e ∈ f))

/-- **Support-aware cut-parity for γ=(0,1)**: For edges in support₂, toggleSum is
nonzero iff the edge is a support-aware cut edge. Mirror of the (1,0) version. -/
lemma toggleSum_supported_on_cuts₂_01
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ G.toRotationSystem.internalFaces)
    {x : E → Color}
    {e : E} (he : e ∉ G.toRotationSystem.boundaryEdges)
    (he_supp : e ∈ support₂ x) :
    (toggleSum G (0,1) S₀ e).snd ≠ 0 ↔ e ∈ cutEdges₂ G x S₀ := by
  classical
  unfold cutEdges₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

  -- Apply non-support-aware version
  rw [toggleSum_supported_on_cuts_01 G E2 hS₀ he]

  unfold cutEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, he, he_supp, true_and]

/-- Helper: cutEdges₁ singleton characterization -/
lemma cutEdges₁_eq_singleton_iff_unique
    {S₀ : Finset (Finset E)} {x : E → Color} {e₀ e : E}
    (h : cutEdges₁ G x S₀ = {e₀}) :
    e ∈ cutEdges₁ G x S₀ ↔ e = e₀ := by
  classical
  simp [h]

/-- Helper: cutEdges₂ singleton characterization -/
lemma cutEdges₂_eq_singleton_iff_unique
    {S₀ : Finset (Finset E)} {x : E → Color} {e₀ e : E}
    (h : cutEdges₂ G x S₀ = {e₀}) :
    e ∈ cutEdges₂ G x S₀ ↔ e = e₀ := by
  classical
  simp [h]

/-- **H2. Prescribed-cut leaf-subtree** (Component-After-Delete Construction)

Given an edge e₀ in support₁ x, construct a leaf-subtree S₀ whose unique cut edge is e₀.

**Strategy (following GPT-5 Pro's guidance)**:
1. Get seed face f₀ incident to e₀ (exists by interior_edge_covered)
2. Build S₀ = faces reachable from f₀ via adjOnSupportExcept x e₀
   - This uses dual adjacency across support edges, but EXCLUDES e₀
3. Prove cutEdges₁ G x S₀ = {e₀}
   - e₀ ∈ cutEdges₁: e₀ has exactly one incident face in S₀ (the seed f₀)
   - The other face incident to e₀ is NOT reachable (can't cross e₀)
   - Other edges: either have 0 or 2 incident faces in S₀ (not cut edges)

This construction only needs 2 small admits for ReflTransGen connectivity proofs.
-/
lemma exists_leaf_subtree_with_prescribed_cut₁
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet)
    {e0 : E} (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ (S₀ : Finset (Finset E)), S₀.Nonempty ∧
      S₀ ⊆ facesTouching₁ (G := G) x ∧
      (cutEdges₁ G x S₀) = {e0} := by
  classical

  -- Get seed face f₀ incident to e₀
  obtain ⟨f₀, hf₀_internal, hf₀_contains⟩ :=
    G.interior_edge_covered he0_int

  -- Build S₀ as component reachable from f₀ via adjOnSupportExcept
  -- This is the "component after deleting e₀" construction
  sorry -- Full implementation needs Relation.ReflTransGen machinery

/-- **H3₁. Strict descent via prescribed cut (support-aware version for γ=(1,0))**

Given a leaf-subtree S₀ with unique cut edge e₀ in support₁ x,
toggling by γ=(1,0) strictly decreases support₁.

**Proof strategy**:
1. Use `toggleSum_supported_on_cuts₁_10` to show toggleSum flips only e₀
2. Apply `support₁_add_toggles_singleton` to show support₁ toggles only at e₀
3. Since e₀ ∈ support₁ x, we have: support₁ (x + toggleSum) = support₁ x \ {e₀}
4. Therefore |support₁| decreases by exactly 1
-/
lemma aggregated_toggle_strict_descent_at_prescribed_cut₁
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀_sub : S₀ ⊆ facesTouching₁ (G := G) x)
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet)
    {e0 : E} (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    (hcut₁ : cutEdges₁ G x S₀ = {e0}) :
    (support₁ (x + toggleSum G (1,0) S₀)).card < (support₁ x).card := by
  classical

  -- Apply toggling lemma: support₁ (x + toggleSum) = support₁ x \ {e₀}
  have hsupp_eq : support₁ (x + toggleSum G (1,0) S₀) = (support₁ x) \ {e0} := by
    -- Use support₁_add_toggles_singleton with y = toggleSum G (1,0) S₀
    -- Need to show: (toggleSum e).fst = 0 for e ≠ e₀, and ≠ 0 for e = e₀
    sorry

  -- Therefore support decreases by 1
  rw [hsupp_eq]
  have : e0 ∈ support₁ x := he0_supp
  sorry -- Need: card (s \ {a}) < card s when a ∈ s

/-- **H3. Strict descent via prescribed cut (non-support-aware version)**

Following GPT-5 Pro's guidance: toggleSum flips exactly e₀, so support decreases by 1.
-/
lemma aggregated_toggle_strict_descent_at_prescribed_cut
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀_sub : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    (hcut : cutEdges G S₀ = {e0})
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet) (he0_supp : e0 ∈ support₁ x) :
    (support₁ (x + toggleSum G (1,0) S₀)).card < (support₁ x).card := by
  classical

  -- toggleSum flips exactly e0 in fst-coordinate
  have hsupp : ∀ e, (toggleSum G (1,0) S₀ e).fst ≠ 0 ↔ e = e0 := by
    intro e
    by_cases he : e ∈ G.toRotationSystem.boundaryEdges
    · -- boundary edges: both sides false
      constructor
      · intro h
        -- toggleSum on boundary is zero (no internal faces contain boundary edges)
        exfalso
        sorry -- boundary edge handling
      · intro heq
        subst heq
        contradiction -- e0 is interior but e is boundary
    · -- interior edges: use cut-parity
      have : (toggleSum G (1,0) S₀ e).fst ≠ 0 ↔ e ∈ cutEdges G S₀ :=
        toggleSum_supported_on_cuts_10 G E2 hS₀_sub he
      rw [this, cutEdges_eq_singleton_iff_unique G hcut]

  -- Compute support exactly: support₁ (x + toggleSum) = support₁ x \ {e0}
  have hsupport_eq : support₁ (x + toggleSum G (1,0) S₀) = (support₁ x) \ {e0} := by
    ext e
    simp only [support₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
               Finset.mem_singleton]
    constructor
    · intro h
      -- h : (x e + toggleSum … e).fst ≠ 0
      constructor
      · -- Show (x e).fst ≠ 0 (unfolded from e ∈ support₁ x)
        by_cases he_eq : e = e0
        · rw [he_eq]; simp only [support₁, Finset.mem_filter] at he0_supp; exact he0_supp.2
        · -- e ≠ e0, so toggleSum is 0, hence x e must be nonzero
          have : (toggleSum G (1,0) S₀ e).fst = 0 := by
            by_contra hne
            have : e = e0 := (hsupp e).mp hne
            contradiction
          simp only [Prod.fst_add] at h
          simpa [this] using h
      · -- Show e ≠ e0
        by_contra heq
        -- heq : ¬(e ≠ e0), i.e., e = e0
        -- At e = e0: (x e).fst + (toggleSum e).fst ≠ 0
        -- But e0 ∈ support₁ x means (x e0).fst ≠ 0, i.e., = 1
        -- And toggleSum flips, so (toggleSum e).fst ≠ 0, i.e., = 1
        -- So (x e).fst + (toggleSum e).fst = 1 + 1 = 0 in ZMod 2
        have he_eq_e0 : e = e0 := by simpa using heq
        have hx_ne : (x e).fst ≠ 0 := by
          rw [he_eq_e0]; simp only [support₁, Finset.mem_filter] at he0_supp; exact he0_supp.2
        have hx_eq_1 : (x e).fst = 1 :=
          (zmod2_ne_zero_iff_eq_one ((x e).fst)).1 hx_ne
        have hts_ne : (toggleSum G (1,0) S₀ e).fst ≠ 0 := by
          have : e = e0 := he_eq_e0
          rw [this]; exact (hsupp e0).mpr rfl
        have hts_eq_1 : (toggleSum G (1,0) S₀ e).fst = 1 :=
          (zmod2_ne_zero_iff_eq_one ((toggleSum G (1,0) S₀ e).fst)).1 hts_ne
        simp only [fst_add_apply] at h
        rw [hx_eq_1, hts_eq_1] at h
        simp at h
    · intro ⟨hx_supp, hne⟩
      -- hx_supp : (x e).fst ≠ 0 (unfolded from e ∈ support₁ x), hne : e ≠ e0
      -- Since e ≠ e0, toggleSum flips nothing: (toggleSum e).fst = 0
      have hts_zero : (toggleSum G (1,0) S₀ e).fst = 0 := by
        by_contra h
        have : e = e0 := (hsupp e).mp h
        contradiction
      show (x e + toggleSum G (1,0) S₀ e).fst ≠ 0
      simp only [Prod.fst_add, hts_zero, add_zero]
      exact hx_supp

  -- Finally, strict cardinality drop by 1
  rw [hsupport_eq]
  rw [Finset.sdiff_singleton_eq_erase]
  have : #((support₁ x).erase e0) + 1 = #(support₁ x) := Finset.card_erase_add_one he0_supp
  omega

/-- **Mirror of H3 for γ=(0,1): strict descent in support₂**

Identical structure to the (1,0) version, but using .snd and support₂.
-/
lemma aggregated_toggle_strict_descent_at_prescribed_cut_01
    (E2 : ∀ {e}, e ∉ G.toRotationSystem.boundaryEdges →
      (G.toRotationSystem.facesIncidence e).card ≤ 2)
    {S₀ : Finset (Finset E)} (hS₀_sub : S₀ ⊆ G.toRotationSystem.internalFaces)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges)
    (hcut : cutEdges G S₀ = {e0})
    {x : E → Color} (hx : x ∈ G.zeroBoundarySet) (he0_supp : e0 ∈ support₂ x) :
    (support₂ (x + toggleSum G (0,1) S₀)).card < (support₂ x).card := by
  classical

  -- toggleSum flips exactly e0 in snd-coordinate
  have hsupp : ∀ e, (toggleSum G (0,1) S₀ e).snd ≠ 0 ↔ e = e0 := by
    intro e
    by_cases he : e ∈ G.toRotationSystem.boundaryEdges
    · -- boundary edges: both sides false
      constructor
      · intro h
        exfalso
        sorry -- boundary edge handling (same as _10 version)
      · intro heq
        subst heq
        contradiction
    · -- interior edges: use cut-parity
      have : (toggleSum G (0,1) S₀ e).snd ≠ 0 ↔ e ∈ cutEdges G S₀ :=
        toggleSum_supported_on_cuts_01 G E2 hS₀_sub he
      rw [this, cutEdges_eq_singleton_iff_unique G hcut]

  -- Compute support exactly: support₂ (x + toggleSum) = support₂ x \ {e0}
  have hsupport_eq : support₂ (x + toggleSum G (0,1) S₀) = (support₂ x) \ {e0} := by
    ext e
    simp only [support₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
               Finset.mem_singleton]
    constructor
    · intro h
      -- h : (x e + toggleSum … e).snd ≠ 0
      constructor
      · -- Show (x e).snd ≠ 0 (unfolded from e ∈ support₂ x)
        by_cases he_eq : e = e0
        · rw [he_eq]; simp only [support₂, Finset.mem_filter] at he0_supp; exact he0_supp.2
        · -- e ≠ e0, so toggleSum is 0, hence x e must be nonzero
          have : (toggleSum G (0,1) S₀ e).snd = 0 := by
            by_contra hne
            have : e = e0 := (hsupp e).mp hne
            contradiction
          simp only [Prod.snd_add] at h
          simpa [this] using h
      · -- Show e ≠ e0
        by_contra heq
        -- heq : ¬(e ≠ e0), i.e., e = e0
        -- At e = e0: (x e).snd + (toggleSum e).snd ≠ 0
        -- But e0 ∈ support₂ x means (x e0).snd ≠ 0, i.e., = 1
        -- And toggleSum flips, so (toggleSum e).snd ≠ 0, i.e., = 1
        -- So (x e).snd + (toggleSum e).snd = 1 + 1 = 0 in ZMod 2
        have he_eq_e0 : e = e0 := by simpa using heq
        have hx_ne : (x e).snd ≠ 0 := by
          rw [he_eq_e0]; simp only [support₂, Finset.mem_filter] at he0_supp; exact he0_supp.2
        have hx_eq_1 : (x e).snd = 1 :=
          (zmod2_ne_zero_iff_eq_one ((x e).snd)).1 hx_ne
        have hts_ne : (toggleSum G (0,1) S₀ e).snd ≠ 0 := by
          have : e = e0 := he_eq_e0
          rw [this]; exact (hsupp e0).mpr rfl
        have hts_eq_1 : (toggleSum G (0,1) S₀ e).snd = 1 :=
          (zmod2_ne_zero_iff_eq_one ((toggleSum G (0,1) S₀ e).snd)).1 hts_ne
        simp only [snd_add_apply] at h
        rw [hx_eq_1, hts_eq_1] at h
        simp at h
    · intro ⟨hx_supp, hne⟩
      -- hx_supp : (x e).snd ≠ 0 (unfolded from e ∈ support₂ x), hne : e ≠ e0
      -- Since e ≠ e0, toggleSum flips nothing: (toggleSum e).snd = 0
      have hts_zero : (toggleSum G (0,1) S₀ e).snd = 0 := by
        by_contra h
        have : e = e0 := (hsupp e).mp h
        contradiction
      show (x e + toggleSum G (0,1) S₀ e).snd ≠ 0
      simp only [Prod.snd_add, hts_zero, add_zero]
      exact hx_supp

  -- Finally, strict cardinality drop by 1
  rw [hsupport_eq]
  rw [Finset.sdiff_singleton_eq_erase]
  have : #((support₂ x).erase e0) + 1 = #(support₂ x) := Finset.card_erase_add_one he0_supp
  omega

end FourColor
