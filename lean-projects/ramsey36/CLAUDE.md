# Ramsey R(3,6) = 18 Formalization

## Project Goal

Formalize David Cariolaro's elementary proof that R(3,6) = 18.

**Paper**: "On the Ramsey number R(3,6)", Australian J. Combinatorics 37 (2007), 301-305

## Formalization Rules

- Always prove that which can be proven without using axioms. No exceptions.
- Never use sorries as a substitute for axioms. A sorry is never well-justified.
- Build a solid foundation of concretely proven theorems/lemmas.
- Clean code invariants: zero warnings (beyond sorries), zero axioms, zero errors.

## Build Rules - CRITICAL

**READ THIS BEFORE ANY BUILD OPERATION**

### Mathlib Pinning Rules

⚠️ **NEVER run `lake update`** unless intentionally upgrading mathlib
- mathlib is pinned to commit `06d95e5f5311594940c0c3dff5381fabe4fcabe7`
- Lean version: `v4.24.0-rc1`
- Declared in `lakefile.toml` and mirrored in `lake-manifest.json`
- Breaking this pin will force mathlib rebuild from source (hours of work)

### CPU-Friendly Build Rules

⚠️ **ALWAYS limit concurrent jobs** to keep CPU usage manageable

#### Preferred Method (Use This):
```bash
export LAKE_JOBS=3
nice -n 19 lake build <target>
```

#### NEVER DO THIS:
```bash
lake build <target>  # No job limit - will use all CPUs!
lake clean           # Deletes ALL build artifacts including mathlib! Hours to rebuild!
```

### Build Commands

#### Quick build of main file:
```bash
export LAKE_JOBS=3 && lake build Ramsey36.Basic
```

#### Full project build:
```bash
export LAKE_JOBS=3 && nice -n 19 lake build
```

#### Check specific file without full build:
```bash
# Just check syntax, don't build dependencies
lean Ramsey36/Basic.lean
```

### Fresh Setup (No Mathlib Rebuild)

```bash
lake exe cache get  # Download prebuilt mathlib cache
lake build          # Build project only
```

### Key Points

1. **LAKE_JOBS=3** keeps CPU usage under ~75% (user friendly)
2. **No limit** = 100% CPU sustained, computer unusable
3. **Never** run multiple builds in parallel
4. **Never** break mathlib pin without coordination

## Project Structure

```
Ramsey36/
├── Basic.lean          # Main definitions and theorem statements
├── Critical17.lean     # The 17-vertex counterexample (TODO)
├── Claim1.lean         # 5-regularity proof (TODO)
├── Claim2.lean         # Neighborhood structure (TODO)
├── Claim3.lean         # 4-cycle proof (TODO)
└── Final.lean          # Final contradiction (TODO)
```

## Current Status

### Completed
- ✅ Project setup with mathlib pinned to match fourcolor
- ✅ Basic definitions in `Ramsey36/Basic.lean`:
  - `ramseyNumber` - The Ramsey number definition
  - `HasRamseyProperty` - Graph has K_k or IS_l
  - `TriangleFree` - No 3-cliques
  - `NoKIndepSet` - No k-independent set
  - `commonNeighborsCard` - Neighborhood intersection counting
  - All main claims structured with sorries

### TODO (Following Paper Roadmap)
- [ ] Implement `criticalGraph17` from paper Figure 1
- [ ] Prove `criticalGraph17_triangleFree` (decidable computation)
- [ ] Prove `criticalGraph17_no_6_indep` (decidable computation)
- [ ] **Lower bound** (R(3,6) ≥ 18): Use critical graph
- [ ] **Claim 1**: 5-regularity using R(3,5) = 14
- [ ] **Claim 2**: Neighborhood structure (4 + 8 split)
- [ ] **Claim 3**: p-vertices form 4-cycle
- [ ] **Final**: Exhaustive case analysis → contradiction
- [ ] **Upper bound** (R(3,6) ≤ 18): Combine all claims

## Mathlib Infrastructure Available

Based on survey of `Mathlib.Combinatorics.SimpleGraph.*`:

### ✅ Available (Use These)
- `SimpleGraph` - Basic graph structure
- `IsClique`, `IsNClique`, `CliqueFree` - Clique predicates
- `IsIndepSet`, `IsNIndepSet`, `IndepSetFree` - Independent set predicates
- `neighborSet`, `neighborFinset` - Vertex neighborhoods
- `commonNeighbors` - Neighborhood intersection
- `degree`, `IsRegularOfDegree` - Degree operations
- `isIndepSet_neighborSet_of_triangleFree` - Key lemma for triangles
- `sum_degrees_eq_twice_card_edges` - Handshaking lemma

### ⚠️ Need to Define
- Ramsey number itself (defined in Basic.lean)
- R(3,5) = 14 (prerequisite - may axiomatize or formalize)
- The 17-vertex critical graph
- Specific counting arguments for Claim 2

## Key Insights for Formalization

### 1. Decidability is Your Friend
With `Fin 18`, everything is decidable! Use:
```lean
decide  -- For concrete computations
fin_cases  -- For exhaustive case analysis
```

### 2. Use Finset for Cardinality
```lean
def commonNeighborsCard (G : SimpleGraph α) [LocallyFinite G] (v w : α) : ℕ :=
  (G.neighborFinset v ∩ G.neighborFinset w).card
```

### 3. Leverage Mathlib Lemmas
- `isClique_compl` - Convert between complements
- `degree_compl` - Degree in complement graph
- `IsRegularOfDegree.compl` - Regularity transfers

### 4. The Final Step Will Be Ugly
Accept that the last contradiction involves:
- 18 labeled vertices
- Many subcases
- Lots of "by symmetry" reasoning

**Solution**: Break it into MANY small lemmas, use automation aggressively.

## Estimated Effort

Based on `FORMALIZATION_ROADMAP.md`:
- **LOC**: 800-1200 lines
- **Time**: 7-10 weeks for experienced Lean developer
- **Difficulty**: ⭐⭐⭐ Medium (similar to Four Color infrastructure, much shorter proof)

## Working Through "Hard" Problems

When you encounter something that seems difficult:

**Don't say "this is hard" as a reason to stop.**

Instead:
1. **Search and investigate** - Use Grep, Read, and exploration to understand what exists
2. **Break it down** - What are the actual concrete steps needed?
3. **Document with sorry** - Convert the "hard" thing into a theorem with a clear TODO comment
4. **Trust the process** - Often what seems hard becomes clear once you start

**Key insight**: "Hard" usually just means "I haven't searched/explored enough yet."

## References

1. David Cariolaro. On the Ramsey number R(3,6). Australian J. Combinatorics 37 (2007), 301-305.
2. [Radziszowski's Dynamic Survey on Small Ramsey Numbers](http://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1)
3. `PAPER_ANALYSIS.md` - Detailed feasibility analysis
4. `FORMALIZATION_ROADMAP.md` - Week-by-week implementation plan
