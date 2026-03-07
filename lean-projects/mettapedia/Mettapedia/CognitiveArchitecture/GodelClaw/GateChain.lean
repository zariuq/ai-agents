import Mettapedia.CognitiveArchitecture.GodelClaw.PolicyKernel

/-!
# GodelClaw Gate Chain: Decision Policy

Lean formalization of the 6-gate conjunction from `vericore-policy/src/gate_chain.rs`.

The gate chain is a strict AND: all gates must allow for an action to proceed.
Order: schedule → action_kind → tool_id → skill_id → ingress → primitive.

This module also provides a generic `GateChain` structure parameterized by
the number and type of gates, so the specific 6-gate instance is just one
configuration.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.GateChain

/-! ## Generic gate chain -/

/-- A gate is a boolean decision function over some context. -/
abbrev Gate (Ctx : Type*) := Ctx → Bool

/-- A gate chain is a list of gates. The chain allows iff all gates allow. -/
def chainAllows {Ctx : Type*} (gates : List (Gate Ctx)) (ctx : Ctx) : Bool :=
  gates.all (· ctx)

/-- Any single deny means the chain denies. -/
theorem chainAllows_false_of_mem_false {Ctx : Type*}
    (gates : List (Gate Ctx)) (ctx : Ctx) (g : Gate Ctx)
    (hMem : g ∈ gates) (hDeny : g ctx = false) :
    chainAllows gates ctx = false := by
  simp [chainAllows]
  exact ⟨g, hMem, by simp [hDeny]⟩

/-- Chain allow implies every gate allowed. -/
theorem chainAllows_implies_all {Ctx : Type*}
    (gates : List (Gate Ctx)) (ctx : Ctx)
    (h : chainAllows gates ctx = true) (g : Gate Ctx)
    (hMem : g ∈ gates) : g ctx = true := by
  simp [chainAllows] at h
  exact h g hMem

/-- Empty chain always allows. -/
theorem chainAllows_nil {Ctx : Type*} (ctx : Ctx) :
    chainAllows ([] : List (Gate Ctx)) ctx = true := rfl

/-! ## VeriCore's specific 6-gate chain -/

/-- The 6-gate conjunction, matching the Verus `spec_gate_chain_allows`. -/
def sixGateAllows
    (schedule actionKind toolId skillId ingress primitive : Bool) : Bool :=
  schedule && actionKind && toolId && skillId && ingress && primitive

/-- All allow → chain allows. -/
theorem sixGate_all_true :
    sixGateAllows true true true true true true = true := rfl

/-- Schedule deny blocks everything. -/
theorem sixGate_schedule_deny
    (ak ti si ig pr : Bool) :
    sixGateAllows false ak ti si ig pr = false := rfl

/-- Ingress deny blocks even if primitive allows. -/
theorem sixGate_ingress_deny
    (sc ak ti si pr : Bool) :
    sixGateAllows sc ak ti si false pr = false := by
  simp [sixGateAllows]

/-- Any single false gate denies the chain. -/
theorem sixGate_any_deny (sc ak ti si ig pr : Bool)
    (h : sixGateAllows sc ak ti si ig pr = true) :
    sc = true ∧ ak = true ∧ ti = true ∧ si = true ∧ ig = true ∧ pr = true := by
  cases sc <;> cases ak <;> cases ti <;> cases si <;> cases ig <;> cases pr <;>
    simp_all [sixGateAllows]

end Mettapedia.CognitiveArchitecture.GodelClaw.GateChain
