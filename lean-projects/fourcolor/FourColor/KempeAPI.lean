import FourColor.Triangulation
import FourColor.Geometry.Disk
import FourColor.Tait

/-!
# Kempe Chain API Shims

This module provides a unified API for Kempe chain operations, centralizing
all naming differences between the implementation and the theoretical framework.

The actual proofs in KempeExistence.lean reference these definitions, making
it easy to adapt to changes in the underlying implementation.
-/

namespace FourColor

open Classical

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Chain type: edge labeling in F₂×F₂ -/
abbrev Chain (E : Type*) := E → Color

/-- Zero-boundary predicate -/
def InZero {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (x : E → Color) : Prop :=
  x ∈ D.zeroBoundarySet

/-- Properness at a single vertex: all incident edges have different colors -/
def taitProperAt {V E : Type*} [Fintype V] [Fintype E]
    (incident : V → Finset E) (v : V) (x : E → Color) : Prop :=
  ∀ e₁ e₂, e₁ ∈ incident v → e₂ ∈ incident v → e₁ ≠ e₂ →
    x e₁ ≠ x e₂

/-- Global properness: proper at all vertices -/
def taitProper {V E : Type*} [Fintype V] [Fintype E]
    (incident : V → Finset E) (x : E → Color) : Prop :=
  ∀ v, taitProperAt incident v x

/-- Support of a chain: edges with nonzero color -/
def supp {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) : Finset E :=
  Finset.univ.filter (fun e => x e ≠ (0, 0))

/-- Set of "bad" vertices where properness fails -/
def badVerts {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (incident : V → Finset E) (x : E → Color) : Finset V :=
  Finset.univ.filter (fun v => ¬taitProperAt incident v x)

@[simp] lemma mem_badVerts {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (incident : V → Finset E) (x : E → Color) {v : V} :
    v ∈ badVerts incident x ↔ ¬taitProperAt incident v x := by
  simp [badVerts]

/-- Basic Kempe switch operation -/
def kempeSwitch {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (x : E → Color)
    (c₁ c₂ : Color)
    (chain : Finset E) : E → Color :=
  fun e => if e ∈ chain then
    if x e = c₁ then c₂
    else if x e = c₂ then c₁
    else x e
  else x e

/-- Extract colors that witness non-properness at a vertex -/
def colorsAtBadVertex {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (incident : V → Finset E) (v : V) (x : E → Color)
    (hv : v ∈ badVerts incident x) : Color × Color :=
  classical
  -- v is bad means ¬taitProperAt, i.e., ∃ e₁ e₂ distinct incident edges with same color
  have : ∃ e₁ e₂, e₁ ∈ incident v ∧ e₂ ∈ incident v ∧ e₁ ≠ e₂ ∧ x e₁ = x e₂ := by
    simp [mem_badVerts, taitProperAt] at hv
    push_neg at hv
    exact hv
  let e₁ := Classical.choose this
  let e₂ := Classical.choose (Classical.choose_spec this)
  (x e₁, x e₂)

/-- Kempe chain through a vertex for a pair of colors -/
def kempeChain {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (x : E → Color)
    (v : V)
    (c₁ c₂ : Color) : Finset E :=
  -- For now: all edges colored c₁ or c₂ (conservative overapproximation)
  -- TODO: implement proper connected component reachability
  classical
  Finset.univ.filter (fun e => x e = c₁ ∨ x e = c₂)

/-- Kempe fix: switch along a chain through a bad vertex -/
def kempeFix {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (x : E → Color)
    (v : V) : E → Color :=
  classical
  if hv : v ∈ badVerts incident x then
    let (c₁, c₂) := colorsAtBadVertex incident v x hv
    let chain := kempeChain incident x v c₁ c₂
    kempeSwitch incident x c₁ c₂ chain
  else
    -- v is not bad, return x unchanged
    x

/-- Kempe switch preserves zero-boundary property -/
lemma kempeSwitch_preserves_zero {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E)
    (x : E → Color)
    (c₁ c₂ : Color)
    (chain : Finset E)
    (hx : InZero D x) :
    InZero D (kempeSwitch D.incident x c₁ c₂ chain) := by
  sorry  -- Wire to your existing sum_mem_zero + closure lemmas

/-- Kempe fix preserves zero-boundary -/
lemma kempeFix_preserves_zero {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E)
    (x : E → Color)
    (v : V)
    (hx : InZero D x) :
    InZero D (kempeFix D.incident x v) := by
  unfold kempeFix
  apply kempeSwitch_preserves_zero
  exact hx

end FourColor
