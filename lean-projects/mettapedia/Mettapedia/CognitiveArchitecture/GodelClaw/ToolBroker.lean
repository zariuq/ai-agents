import Mettapedia.CognitiveArchitecture.GodelClaw.GateChain

/-!
# GodelClaw Tool Broker: Authorization & Capability Identity

Lean formalization of the tool broker invariants from
`vericore-policy/src/tool_broker.rs` and `vericore-policy/src/tool_policy.rs`.

Covers:
- Tool authorization (allowlist + wildcard)
- Origin-irrelevant gating (native vs brokered same decision)
- Native name shadow denial
- Capability ID stability (mcp:server:tool format)
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.ToolBroker

/-! ## Tool authorization -/

/-- A tool is authorized if the wildcard is present or the capability ID is in the allowlist.
    Matches Verus `spec_tool_authorized`. -/
def toolAuthorized (inAllowlist wildcard : Bool) : Bool :=
  wildcard || inAllowlist

/-- Wildcard allows all tools. -/
theorem wildcard_allows_all (inAllowlist : Bool) :
    toolAuthorized inAllowlist true = true := by
  simp [toolAuthorized]

/-- Unknown capability without wildcard is denied. -/
theorem unknown_denied :
    toolAuthorized false false = false := rfl

/-- Listed capability is always authorized. -/
theorem listed_authorized (wildcard : Bool) :
    toolAuthorized true wildcard = true := by
  simp [toolAuthorized]

/-! ## Origin-irrelevant authorization -/

/-- Authorization depends only on allowlist membership and wildcard, not on origin.
    Two tools with the same (inAllowlist, wildcard) get the same result,
    regardless of whether they are native or brokered. -/
theorem origin_irrelevant (inAllowlist wildcard : Bool) :
    toolAuthorized inAllowlist wildcard = toolAuthorized inAllowlist wildcard := rfl

/-- More substantively: for any fixed policy state (wildcard, allowlist membership),
    the authorization decision is identical for native and brokered tools. -/
theorem origin_irrelevant_nat_vs_brokered
    (nativeInList brokeredInList wildcard : Bool)
    (h : nativeInList = brokeredInList) :
    toolAuthorized nativeInList wildcard = toolAuthorized brokeredInList wildcard := by
  rw [h]

/-! ## Native name shadow denial -/

/-- A brokered tool that shadows a native tool name must be denied.
    Matches Verus `spec_native_shadow_denied`. -/
def nativeShadowDenied (isBrokered displayNameMatchesNative : Bool) : Bool :=
  !(isBrokered && displayNameMatchesNative)

/-- Brokered + native collision → denied. -/
theorem shadow_collision_denied :
    nativeShadowDenied true true = false := rfl

/-- Native tools are never shadow-denied. -/
theorem native_not_shadow_denied (displayNameMatches : Bool) :
    nativeShadowDenied false displayNameMatches = true := by
  simp [nativeShadowDenied]

/-- Brokered tools with non-colliding names are not shadow-denied. -/
theorem non_colliding_brokered_ok :
    nativeShadowDenied true false = true := rfl

/-! ## Combined tool gate -/

/-- Full tool gate: shadow check AND authorization.
    Matches Verus `spec_tool_gate_allows`. -/
def toolGateAllows (isBrokered displayNameMatchesNative inAllowlist wildcard : Bool) : Bool :=
  nativeShadowDenied isBrokered displayNameMatchesNative &&
  toolAuthorized inAllowlist wildcard

/-- Shadow collision blocks even authorized tools. -/
theorem shadow_blocks_authorized :
    toolGateAllows true true true true = false := rfl

/-- Non-colliding authorized brokered tool is allowed. -/
theorem non_colliding_authorized :
    toolGateAllows true false true false = true := rfl

/-- Native authorized tool always passes the tool gate. -/
theorem native_authorized_passes (inAllowlist wildcard : Bool)
    (h : toolAuthorized inAllowlist wildcard = true) :
    toolGateAllows false false inAllowlist wildcard = true := by
  simp [toolGateAllows, nativeShadowDenied, h]

/-! ## Interaction with the 6-gate chain -/

open GateChain in
/-- If the tool gate denies (tool_id = false), the full 6-gate chain denies.
    This connects tool_policy to gate_chain. -/
theorem tool_gate_deny_blocks_chain
    (sc ak si ig pr : Bool) :
    sixGateAllows sc ak false si ig pr = false := by
  simp [sixGateAllows]

/-! ## Capability ID stability -/

/-- A capability ID is stable if it has all three components: mcp prefix, server name, tool name.
    Matches Verus `spec_capability_id_stable`. -/
def capabilityIdStable (hasMcpPrefix hasServerName hasToolName : Bool) : Bool :=
  hasMcpPrefix && hasServerName && hasToolName

/-- Missing any component makes the ID unstable. -/
theorem unstable_missing_prefix (hasServer hasTool : Bool) :
    capabilityIdStable false hasServer hasTool = false := rfl

theorem unstable_missing_server (hasPrefix hasTool : Bool) :
    capabilityIdStable hasPrefix false hasTool = false := by
  simp [capabilityIdStable]

theorem unstable_missing_tool (hasPrefix hasServer : Bool) :
    capabilityIdStable hasPrefix hasServer false = false := by
  simp [capabilityIdStable]

/-- Complete capability ID is stable. -/
theorem complete_id_stable :
    capabilityIdStable true true true = true := rfl

end Mettapedia.CognitiveArchitecture.GodelClaw.ToolBroker
