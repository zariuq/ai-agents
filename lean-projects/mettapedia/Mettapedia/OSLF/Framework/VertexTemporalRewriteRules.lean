import Mettapedia.OSLF.Framework.VertexRewriteRules

/-!
# Vertex-Parameterized Temporal/Event Rewrite Extension

This module extends the selector-only per-vertex language with a compact,
always-enabled temporal/event rewrite fragment.

Design:
- Keep existing selector activation (`activeRules`) unchanged.
- Add three temporal/event rewrite rules at every vertex.
- Preserve monotonicity along the hypercube weakness order via append.
-/

namespace Mettapedia.OSLF.Framework.VertexTemporalRewriteRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.ProbabilityTheory.Hypercube
open Mettapedia.OSLF.Framework.VertexRewriteRules

/-! ## Temporal/Event Pattern Vocabulary -/

def pHoldsAt (e t : Pattern) : Pattern := .apply "holdsAt" [e, t]
def pInitiatedAt (e t : Pattern) : Pattern := .apply "initiatedAt" [e, t]
def pTerminatedAt (e t : Pattern) : Pattern := .apply "terminatedAt" [e, t]
def pNext (t : Pattern) : Pattern := .apply "next" [t]

/-! ## Temporal/Event Rules -/

/-- Initiation at time `t` yields holding at `t`. -/
def ruleEventInitiatedImpliesHolds : RewriteRule := {
  name := "PLN_Event_InitiatedImpliesHolds"
  typeContext := [("e", .base "Proc"), ("t", .base "Proc")]
  premises := []
  left := pInitiatedAt (.fvar "e") (.fvar "t")
  right := pHoldsAt (.fvar "e") (.fvar "t")
}

/-- Persistence step: holding at `t` yields holding at `next t`. -/
def ruleEventPersistenceStep : RewriteRule := {
  name := "PLN_Event_PersistenceStep"
  typeContext := [("e", .base "Proc"), ("t", .base "Proc")]
  premises := []
  left := pHoldsAt (.fvar "e") (.fvar "t")
  right := pHoldsAt (.fvar "e") (pNext (.fvar "t"))
}

/-- Termination marker propagation to the next time step. -/
def ruleEventTerminationStep : RewriteRule := {
  name := "PLN_Event_TerminationStep"
  typeContext := [("e", .base "Proc"), ("t", .base "Proc")]
  premises := []
  left := pTerminatedAt (.fvar "e") (.fvar "t")
  right := pTerminatedAt (.fvar "e") (pNext (.fvar "t"))
}

/-- Temporal/event fragment, enabled at every probability-hypercube vertex. -/
def temporalEventRules : List RewriteRule :=
  [ruleEventInitiatedImpliesHolds, ruleEventPersistenceStep, ruleEventTerminationStep]

lemma mem_temporalEventRules_cases {r : RewriteRule}
    (hr : r ∈ temporalEventRules) :
    r = ruleEventInitiatedImpliesHolds ∨
      r = ruleEventPersistenceStep ∨
      r = ruleEventTerminationStep := by
  simpa [temporalEventRules] using hr

lemma temporalEventRule_premises_nil {r : RewriteRule}
    (hr : r ∈ temporalEventRules) :
    r.premises = [] := by
  rcases mem_temporalEventRules_cases hr with hinit | hpersist | hterm
  · subst hinit
    simp [ruleEventInitiatedImpliesHolds]
  · subst hpersist
    simp [ruleEventPersistenceStep]
  · subst hterm
    simp [ruleEventTerminationStep]

/-! ## Vertex Extension -/

/-- Selector rules + temporal/event rules at a hypercube vertex. -/
def activeRulesWithTemporal (v : ProbabilityVertex) : List RewriteRule :=
  activeRules v ++ temporalEventRules

/-- Per-vertex LanguageDef including selector and temporal/event rewrites. -/
def vertexTemporalLanguageDef (v : ProbabilityVertex) : LanguageDef where
  name := "PLNSelectorTemporalVertex"
  types := ["Proc", "Family", "Event", "Time"]
  terms := []
  equations := []
  rewrites := activeRulesWithTemporal v

/-- Monotonicity of the extended active-rule set in the weakness order. -/
theorem activeRulesWithTemporal_subset_of_le {v w : ProbabilityVertex} (h : v ≤ w) :
    ∀ r, r ∈ activeRulesWithTemporal w → r ∈ activeRulesWithTemporal v := by
  intro r hr
  rcases List.mem_append.mp hr with hSel | hTemporal
  · exact List.mem_append.mpr (Or.inl (activeRules_subset_of_le h r hSel))
  · exact List.mem_append.mpr (Or.inr hTemporal)

/-- All extended active rules have empty premise lists. -/
theorem activeRuleWithTemporal_premises_nil {v : ProbabilityVertex} {r : RewriteRule}
    (hr : r ∈ activeRulesWithTemporal v) :
    r.premises = [] := by
  rcases List.mem_append.mp hr with hSel | hTemporal
  · exact activeRule_premises_nil hSel
  · exact temporalEventRule_premises_nil hTemporal

example : (activeRulesWithTemporal classicalLogic).length = 6 := by decide
example : (activeRulesWithTemporal quantum).length = 4 := by decide

end Mettapedia.OSLF.Framework.VertexTemporalRewriteRules
