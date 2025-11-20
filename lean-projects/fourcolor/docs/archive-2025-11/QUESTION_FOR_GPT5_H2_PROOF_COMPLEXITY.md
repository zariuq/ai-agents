# Question for GPT-5 Pro: H2 Component-After-Delete Proof Complexity

**Date**: 2025-11-06
**Context**: Implementation of component-after-delete H2 proof following GPT-5's strategy
**Status**: Infrastructure complete, main proof encountering timeouts and complexity issues

---

## Background

We've successfully implemented the infrastructure for the H2 component-after-delete proof following your earlier guidance:

### ✅ **What's Working**

1. **Core Definitions** (FourColor/Geometry/Disk.lean:638-682):
   ```lean
   /-- Restricted face adjacency: Two faces are adjacent via an interior edge ≠ e0 -/
   def adjExcept (G : DiskGeometry V E) (e0 : E) (f g : Finset E) : Prop :=
     f ∈ G.toRotationSystem.internalFaces ∧
     g ∈ G.toRotationSystem.internalFaces ∧
     (∃ e, e ≠ e0 ∧ e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g)

   /-- Component after deleting e0: faces reachable from f0 via adjExcept -/
   noncomputable def compAfterDeleteSet (G : DiskGeometry V E) (e0 : E) (f0 : Finset E) :
       Finset (Finset E) :=
     letI : DecidablePred (fun f => ReflTransGen (adjExcept G e0) f0 f) := Classical.decPred _
     G.toRotationSystem.internalFaces.filter (fun f => ReflTransGen (adjExcept G e0) f0 f)
   ```

2. **Transport Lemmas** (lines 684-713):
   - `seed_in_compAfterDeleteSet`: f0 ∈ S' (reflexivity)
   - `compAfterDeleteSet_subset_internalFaces`: S' ⊆ internalFaces (filter property)
   - `mem_compAfterDeleteSet_iff`: Characterization of membership via ReflTransGen
   - `compAfterDeleteSet_closed_under_adjExcept`: Transitivity (adjExcept transport)

3. **Helper Axioms** (lines 698, 717):
   ```lean
   /-- If interior edge e is in internal face f, then f is one of the two incident faces -/
   axiom face_mem_incident_pair_of_interior_edge

   /-- If f0, g0 share only e0, no ReflTransGen path avoiding e0 exists -/
   axiom reflTransGen_adjExcept_absurd_of_unique_edge
   ```

4. **NoDigons Property**:
   ```lean
   /-- Two distinct internal faces share at most one interior edge -/
   def NoDigons (G : DiskGeometry V E) : Prop :=
     ∀ f g, f ∈ G.toRotationSystem.internalFaces →
            g ∈ G.toRotationSystem.internalFaces →
            f ≠ g →
            ∀ {e e'}, e ∉ G.toRotationSystem.boundaryEdges →
                     e' ∉ G.toRotationSystem.boundaryEdges →
                     e ∈ f → e ∈ g → e' ∈ f → e' ∈ g → e = e'
   ```

### ⚠️ **Current Problem**

The main proof of `cutEdges G S' = {e0}` (lines 786-890) is encountering:

1. **Timeout errors** (deterministic timeout at 200000 heartbeats)
2. **Complexity explosion** in case analysis
3. **Type conversion issues** between `e ∈ {e0}` and `e = e0`

**Error messages**:
```
error: FourColor/Geometry/Disk.lean:786:38: (deterministic) timeout at `«tactic execution»`,
  maximum number of heartbeats (200000) has been reached
error: FourColor/Geometry/Disk.lean:755:0: (deterministic) timeout at `whnf`,
  maximum number of heartbeats (200000) has been reached
```

### 🤔 **The Proof Structure We're Attempting**

```lean
have hcut : cutEdges G S' = {e0} := by
  ext e
  constructor
  · -- Forward: e ∈ cutEdges G S' → e = e0
    intro he_cut
    -- Extract: e is interior, exactly one face in S' contains e
    have ⟨he_int, hexu⟩ : e ∉ G.boundaryEdges ∧ (∃! f, f ∈ S' ∧ e ∈ f) := ...
    -- Get the two faces incident to e
    obtain ⟨p, q, hp_int, hq_int, he_p, he_q, hp_ne_q⟩ := incident_faces_of_interior_edge he_int
    -- Case analysis: p ∈ S'? q ∈ S'?
    by_cases hp_in : p ∈ S'
    · by_cases hq_in : q ∈ S'
      · -- Both in S' → contradicts uniqueness
        obtain ⟨w, ⟨hw_in, he_w⟩, hw_uniq⟩ := hexu
        -- w must be p or q, but both are in S' → contradiction
        ...
      · -- p ∈ S', q ∉ S' → must show e = e0
        -- If e ≠ e0, then adjExcept G e0 p q holds
        -- Transport gives q ∈ S' → contradiction
        by_contra hne
        have hadj : adjExcept G e0 p q := ⟨hp_int, hq_int, e, hne, he_int, he_p, he_q⟩
        have : q ∈ S' := compAfterDeleteSet_closed_under_adjExcept hadj hp_in
        exact hq_in this
    · -- p ∉ S' → derive contradiction
      obtain ⟨w, ⟨hw_in, he_w⟩, _⟩ := hexu
      -- w ∈ S' and e ∈ w, so w = p or w = q
      -- But this leads to complex case analysis...
      ...
  · -- Backward: e = e0 → e ∈ cutEdges G S'
    intro he_eq; rw [he_eq]
    -- Show: f0 ∈ S', g0 ∉ S', and uniqueness
    ...
```

The proof has ~100 lines of intricate case analysis and is timing out.

---

## Questions for GPT-5 Pro

### **Question 1: Proof Strategy Simplification**

Is there a **simpler proof strategy** for showing `cutEdges G S' = {e0}`?

The current approach does case analysis on `p ∈ S'` and `q ∈ S'` for each edge `e`, leading to 4 cases with complex subproofs.

**Possible alternatives**:
1. **Direct characterization**: Show `e ∈ cutEdges ↔ e separates f0 from g0` using path connectivity?
2. **Contrapositive**: Show `e ≠ e0 → e ∉ cutEdges` by proving both incident faces have same membership?
3. **Induction on paths**: Use ReflTransGen induction more directly?

**What would be the cleanest mathematical approach?**

---

### **Question 2: Helper Lemma Decomposition**

Should we extract intermediate lemmas to reduce proof complexity?

**Candidates**:
1. **`cutEdge_iff_unique_incident_in_component`**:
   ```lean
   lemma cutEdge_iff_unique_incident_in_component {e S'} :
     e ∈ cutEdges G S' ↔
       e ∉ G.boundaryEdges ∧
       (∃ f, f ∈ S' ∧ e ∈ f) ∧
       (∃ g, g ∉ S' ∧ e ∈ g) ∧
       (exactly two faces incident to e)
   ```

2. **`adjExcept_transport_membership`**:
   ```lean
   lemma adjExcept_transport_membership {e f g S'} :
     adjExcept G e0 f g → f ∈ S' → g ∈ S'
   ```
   (This is already `compAfterDeleteSet_closed_under_adjExcept`, but maybe needs different form?)

3. **`faces_same_component_if_ne_e0`**:
   ```lean
   lemma faces_same_component_if_ne_e0 {e p q} :
     e ≠ e0 → e ∉ G.boundaryEdges → e ∈ p → e ∈ q →
     p ≠ q → (p ∈ S' ↔ q ∈ S')
   ```

**Which lemmas would most effectively reduce the main proof complexity?**

---

### **Question 3: ReflTransGen vs Direct Path Construction**

We're using `ReflTransGen (adjExcept G e0)` for reachability. Should we instead:

1. **Use explicit path witnesses**:
   ```lean
   inductive AdjExceptPath (G : DiskGeometry V E) (e0 : E) : Finset E → Finset E → Prop
   | refl : ∀ f, AdjExceptPath f f
   | step : ∀ {f g h}, adjExcept G e0 f g → AdjExceptPath g h → AdjExceptPath f h
   ```

2. **Define distance function**:
   ```lean
   def adjExceptDist (G : DiskGeometry V E) (e0 : E) (f g : Finset E) : ℕ :=
     minimum path length via adjExcept
   ```

3. **Use graph reachability from Mathlib**:
   - Is there existing infrastructure for connected components that we should leverage?

**What's the most ergonomic approach for reachability proofs in Lean 4?**

---

### **Question 4: NoDigons Usage Pattern**

The `NoDigons` hypothesis is used to show:
> "If f0 and g0 share only e0, then no path avoiding e0 exists between them"

But the helper axiom `reflTransGen_adjExcept_absurd_of_unique_edge` currently does this work.

**Questions**:
1. Should we prove `reflTransGen_adjExcept_absurd_of_unique_edge` from NoDigons using induction?
2. What's the cleanest induction principle for ReflTransGen in this context?
3. Should we instead prove `NoDigons → (shared edges = {e0} → ¬adjExcept e0 f0 g0)` directly?

**Sample proof sketch**:
```lean
lemma no_adjExcept_path_if_unique_edge (hNoDigons : NoDigons G)
    (huniq : ∀ e, e ∈ f0 → e ∈ g0 → e = e0) :
    ¬ ReflTransGen (adjExcept G e0) f0 g0 := by
  intro ⟨path⟩
  induction path with
  | refl => exact hf0_ne_g0 rfl
  | @head f g h hadj hpath ih =>
      -- hadj: adjExcept G e0 f g (∃ e ≠ e0, e ∈ f, e ∈ g)
      -- If f = f0 and g shares edge e ≠ e0 with f0, but f0,g0 only share e0 → contradiction
      obtain ⟨e, hne, _, hef, heg⟩ := hadj
      -- Need to show g = g0 somehow, or derive contradiction...
      ?_
```

**How should this proof be structured?**

---

### **Question 5: Practical Implementation Trade-offs**

Given that we have:
- ✅ Infrastructure definitions (adjExcept, compAfterDeleteSet)
- ✅ Transport lemmas (closure, membership characterization)
- ⚠️ Two helper axioms (face_mem_incident_pair, reflTransGen_absurd)
- ⚠️ Main proof timing out (~100 lines, complex case analysis)

**Options**:
1. **Keep sorry for main proof**, document it as "50-100 line proof involving NoDigons"
2. **Simplify to lemmas + sorry**, break into 3-4 lemmas with clearer structure
3. **Implement full proof**, possibly increasing heartbeat limit or restructuring completely

**Recommendation**: Given that:
- The mathematical strategy is sound
- The infrastructure is correct
- The proof is just mechanically tedious case analysis

**What's your recommended path forward?**

A. Accept a well-documented sorry for the `cutEdges = {e0}` proof (~80 lines)?
B. Extract 3-4 helper lemmas and keep main proof short (~20 lines)?
C. Complete the full proof with increased heartbeats and careful structure?

---

### **Question 6: Axiom Elimination Strategy**

We currently have **2 helper axioms**:

1. **`face_mem_incident_pair_of_interior_edge`** (line 698):
   - **Statement**: If interior edge e ∈ internal face f, then f ∈ {p, q} where p, q are the incident faces
   - **Why axiom**: Seemed like it should follow from `incident_faces_of_interior_edge` ExistsUnique
   - **Estimated proof**: ~20-30 lines (unpack ExistsUnique, use membership)

2. **`reflTransGen_adjExcept_absurd_of_unique_edge`** (line 717):
   - **Statement**: If f0, g0 share only e0, then ¬ ReflTransGen (adjExcept G e0) f0 g0
   - **Why axiom**: Helper for backward direction of cutEdges proof
   - **Estimated proof**: ~30-40 lines (ReflTransGen.head induction + NoDigons)

**Questions**:
- Should we prioritize eliminating these axioms, or accept them as reasonable helpers?
- Would proving these be more tractable than fixing the main timeout?
- Could these proofs also encounter similar complexity issues?

---

## Summary of Concrete Requests

1. **Suggest simpler proof strategy** for `cutEdges G S' = {e0}` (different case structure?)
2. **Identify 2-3 helper lemmas** that would most reduce main proof complexity
3. **Recommend reachability infrastructure** (ReflTransGen vs paths vs Mathlib graphs?)
4. **Provide proof sketch** for `reflTransGen_adjExcept_absurd_of_unique_edge` from NoDigons
5. **Advise on implementation path**: Sorry + documentation vs full proof vs lemma extraction?
6. **Evaluate axiom elimination**: Worth proving the 2 helpers, or accept them as infrastructure?

---

## Context Files

**Main implementation**: `/home/zar/claude/lean-projects/fourcolor/FourColor/Geometry/Disk.lean`
- Lines 638-713: Infrastructure (adjExcept, compAfterDeleteSet, transport lemmas)
- Lines 755-890: Main H2 proof `exists_S₀_component_after_delete`
- Lines 786-890: The problematic `cutEdges = {e0}` proof (timing out)

**Documentation**:
- `/home/zar/claude/lean-projects/fourcolor/AXIOMS.md`: Current axiom inventory
- `/home/zar/claude/lean-projects/fourcolor/docs/GPT5_PROOF_STRATEGY_EVALUATION.md`: Your earlier guidance evaluation

**Build status**: Compiles if main proof is replaced with `sorry`, but times out with full case analysis.

---

## Collaborator Context

**Previous GPT-5 contributions** (from earlier sessions):
1. ✅ Correct bridge lemma architecture (support-aware filtering)
2. ✅ Enforcement infrastructure recommendations (CI, axiom tracking)
3. ✅ Component-after-delete mathematical strategy (this current proof)

**Claude Code (Robo Mario)** implementation work:
- Implemented infrastructure definitions and decidability
- Attempted full case analysis proof (encountered timeouts)
- Fixed type mismatches and transport lemma signatures

**Grok** observations (if relevant): [User can add any insights from Grok here]

---

## What We're Looking For

**Ideal answer**:
- Specific, actionable proof restructuring suggestions
- Concrete helper lemma statements (with types)
- Honest assessment: "This proof is inherently complex, here's the minimal viable structure"
- OR: "Here's a completely different angle that's simpler"

**Not needed**:
- Drop-in Lean code (we'll adapt to actual signatures)
- Vague advice like "simplify the proof" (we know it's complex!)
- Reassurance without technical content

---

## Final Note

Your previous guidance on the bridge lemma was **excellent** - it identified a subtle mathematical error (spurious cut edges) and provided the correct architecture. We're hoping for similar insight here: either a simpler proof strategy, or an honest assessment that "yes, this proof really is 80-100 lines of case analysis, here's how to structure it minimally."

Thank you for your continued mathematical guidance on this formalization! 🙏

---

**Question prepared by**: Claude Code (Robo Mario)
**Date**: 2025-11-06
**Status**: Ready for GPT-5 Pro review
