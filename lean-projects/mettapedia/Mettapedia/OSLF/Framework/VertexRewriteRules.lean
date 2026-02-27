import Mettapedia.OSLF.Framework.PLNSelectorLanguageDef
import Mettapedia.ProbabilityTheory.Hypercube.Taxonomy

/-!
# Vertex-Parameterized PLN Selector Rules

This module assigns a concrete `LanguageDef` rewrite set to each
`ProbabilityVertex` in the 13-axis hypercube.

Design:
- `ExtBayes2` is always active.
- `ExtBayesFamily` is active exactly on commutative vertices.
- `NormalizeStrength` is active on commutative + precise vertices.

The activation is monotone with respect to the hypercube strength order:
if `v ≤ w` (so `v` is stronger / more specific), then every rule active at `w`
is also active at `v`.
-/

namespace Mettapedia.OSLF.Framework.VertexRewriteRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.ProbabilityTheory.Hypercube
open Mettapedia.OSLF.Framework.PLNSelectorLanguageDef

/-- Family commutation is enabled on commutative vertices. -/
def familyRuleActive (v : ProbabilityVertex) : Prop :=
  v.commutativity = .commutative

instance (v : ProbabilityVertex) : Decidable (familyRuleActive v) :=
  inferInstanceAs (Decidable (v.commutativity = .commutative))

/-- Normalize-strength is enabled on commutative + precise vertices. -/
def normalizeRuleActive (v : ProbabilityVertex) : Prop :=
  v.commutativity = .commutative ∧ v.precision = .precise

instance (v : ProbabilityVertex) : Decidable (normalizeRuleActive v) :=
  inferInstanceAs (Decidable (v.commutativity = .commutative ∧ v.precision = .precise))

/-- Active selector rewrite rules at a hypercube vertex. -/
def activeRules (v : ProbabilityVertex) : List RewriteRule :=
  [ruleExtBayes2] ++
    (if familyRuleActive v then [ruleExtBayesFamily] else []) ++
    (if normalizeRuleActive v then [ruleNormalizeStrength] else [])

/-- The per-vertex PLN selector `LanguageDef`. -/
def vertexLanguageDef (v : ProbabilityVertex) : LanguageDef where
  name := "PLNSelectorVertex"
  types := ["Proc", "Family"]
  terms := []
  equations := []
  rewrites := activeRules v

private lemma comm_bot_of_le {v w : ProbabilityVertex} (h : v ≤ w)
    (hw : w.commutativity = .commutative) : v.commutativity = .commutative := by
  have hle : v.commutativity ≤ w.commutativity := h.1
  rw [hw] at hle
  -- .commutative is ⊥ for CommutativityAxis, so v.comm ≤ ⊥ implies v.comm = ⊥
  exact le_antisymm hle bot_le

private lemma prec_bot_of_le {v w : ProbabilityVertex} (h : v ≤ w)
    (hw : w.precision = .precise) : v.precision = .precise := by
  have hle : v.precision ≤ w.precision := h.2.2.1
  rw [hw] at hle
  exact le_antisymm hle bot_le

lemma familyRuleActive_of_le {v w : ProbabilityVertex} (h : v ≤ w) :
    familyRuleActive w → familyRuleActive v := by
  intro hw
  exact comm_bot_of_le h hw

lemma normalizeRuleActive_of_le {v w : ProbabilityVertex} (h : v ≤ w) :
    normalizeRuleActive w → normalizeRuleActive v := by
  intro ⟨hwcomm, hwprec⟩
  exact ⟨comm_bot_of_le h hwcomm, prec_bot_of_le h hwprec⟩

lemma mem_activeRules_cases {v : ProbabilityVertex} {r : RewriteRule}
    (hr : r ∈ activeRules v) :
    r = ruleExtBayes2 ∨
      (familyRuleActive v ∧ r = ruleExtBayesFamily) ∨
      (normalizeRuleActive v ∧ r = ruleNormalizeStrength) := by
  unfold activeRules at hr
  by_cases hf : familyRuleActive v
  · by_cases hn : normalizeRuleActive v
    · simp [hf, hn] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hf, rfl⟩)
      · exact Or.inr (Or.inr ⟨hn, rfl⟩)
    · simp [hf, hn] at hr
      rcases hr with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨hf, rfl⟩)
  · by_cases hn : normalizeRuleActive v
    · simp [hf, hn] at hr
      rcases hr with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨hn, rfl⟩)
    · simp [hf, hn] at hr
      rcases hr with rfl
      exact Or.inl rfl

lemma activeRule_premises_nil {v : ProbabilityVertex} {r : RewriteRule}
    (hr : r ∈ activeRules v) :
    r.premises = [] := by
  rcases mem_activeRules_cases (v := v) hr with hbase | hfamily | hnorm
  · subst hbase
    simp [ruleExtBayes2]
  · rcases hfamily with ⟨_, hfamily⟩
    subst hfamily
    simp [ruleExtBayesFamily]
  · rcases hnorm with ⟨_, hnorm⟩
    subst hnorm
    simp [ruleNormalizeStrength]

lemma mem_activeRules_base (v : ProbabilityVertex) :
    ruleExtBayes2 ∈ activeRules v := by
  unfold activeRules
  simp

lemma mem_activeRules_family {v : ProbabilityVertex}
    (h : familyRuleActive v) :
    ruleExtBayesFamily ∈ activeRules v := by
  unfold activeRules
  simp [h]

lemma mem_activeRules_normalize {v : ProbabilityVertex}
    (h : normalizeRuleActive v) :
    ruleNormalizeStrength ∈ activeRules v := by
  unfold activeRules
  simp [h]

/-- Activation monotonicity in the hypercube strength order. -/
theorem activeRules_subset_of_le {v w : ProbabilityVertex} (h : v ≤ w) :
    ∀ r, r ∈ activeRules w → r ∈ activeRules v := by
  intro r hr
  rcases mem_activeRules_cases (v := w) hr with hbase | hfamily | hnorm
  · subst hbase
    exact mem_activeRules_base v
  · rcases hfamily with ⟨hw, hEq⟩
    subst hEq
    exact mem_activeRules_family (familyRuleActive_of_le h hw)
  · rcases hnorm with ⟨hw, hEq⟩
    subst hEq
    exact mem_activeRules_normalize (normalizeRuleActive_of_le h hw)

example : (activeRules kolmogorov).length = 3 := by decide

example : (activeRules quantum).length = 1 := by decide

end Mettapedia.OSLF.Framework.VertexRewriteRules
