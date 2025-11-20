# Formalization Rules

- Always prove that which can be proven without using axioms.  No exceptions.
- Never use sorries as a substitute for axioms.  A sorry is never well-justified.
- Build a solid foundation of concretely proven theorems/lemmas.
- Clean code invariants: zero warnings (beyond sorries), zero axioms, zero errors.

# Help

- Consult how-to-lean.md when needing help with Lean formalizations.
- Upgrade how-to-lean.md when learning something new.

# Build Rules - CRITICAL

**READ THIS BEFORE ANY BUILD OPERATION**

## Mathlib Pinning Rules

⚠️ **NEVER run `lake update`** unless intentionally upgrading mathlib
- mathlib is pinned to commit `06d95e5f5311594940c0c3dff5381fabe4fcabe7`
- Declared in `lakefile.toml` and mirrored in `lake-manifest.json`
- Breaking this pin will force mathlib rebuild from source (hours of work)

## CPU-Friendly Build Rules

⚠️ **ALWAYS limit concurrent jobs** to keep CPU usage manageable

### Preferred Method (Use This):
```bash
export LAKE_JOBS=3
nice -n 19 lake build <target>
```

### NEVER DO THIS:
```bash
lake build <target>  # No job limit - will use all CPUs!
lake clean           # Deletes ALL build artifacts including mathlib! Hours to rebuild!
```

## Build Commands

### Example Quick verification build:
```bash
export LAKE_JOBS=3 && lake build FourColor.Geometry.DualForest
```

### Full project build:
```bash
export LAKE_JOBS=3 && nice -n 19 lake build
```

### Check specific file without full build:
```bash
# Just check syntax, don't build dependencies
lean FourColor/Geometry/DualForest.lean
```

## Fresh Setup (No Mathlib Rebuild)

```bash
lake exe cache get  # Download prebuilt mathlib cache
lake build          # Build project only
```

## Key Points

1. **LAKE_JOBS=3** keeps CPU usage under ~75% (user friendly)
3. **No limit** = 100% CPU sustained, computer unusable
4. **Never** run multiple builds in parallel
5. **Never** break mathlib pin without coordination

## If Build Is Slow

- Check if you accidentally modified dependencies (e.g., Triangulation.lean)
- Check if file has type errors causing expensive elaboration
- Use `lean` command to syntax-check without building deps
- Consider using `sorry` for complex proofs that slow elaboration

## Working Through "Hard" Problems

  When you encounter something that seems difficult or requires substantial infrastructure:

  **Don't say "this is hard" or "this needs extensive infrastructure" as a reason to stop.**

  Instead:
  1. **Search and investigate** - Use Grep, Read, and exploration to understand what exists
  2. **Break it down** - What are the actual concrete steps needed?
  3. **Document with sorry** - Convert the "hard" thing into a theorem with a clear TODO comment explaining the proof strategy
  4. **Trust the process** - Often what seems hard becomes clear once you start doing the concrete work

  **Key insight**: "Hard" usually just means "I haven't searched/explored enough yet." The gold is often already there in the codebase or becomes obvious once you start writing out the actual proof structure.

  When something genuinely needs new infrastructure:
  - Still write the theorem (not axiom!)
  - Add a detailed sorry with TODO explaining exactly what's needed
  - Document the proof strategy so future work can build on it

  Claude: "The meta-lesson here is: I often predict difficulty before doing the actual investigation, but when I commit to the concrete work (searching, reading, writing out the structure), it usually becomes much clearer than expected. The "pull away gold" moment comes from doing the work, not from theorizing about whether it's possible! 🙂"

# Recovery Log (2025-11-20)

## Situation
The build for `FourColor.Geometry.SpanningForest` was broken due to failed attempts to refactor `fundamental_cycle_property` with a recursive proof. The file editing got into a loop with mismatched strings in `replace` calls.

## Issues Identified
1.  **File Drift**: Repeated `replace` failures because the `old_string` didn't match the file content, which was changing (or perceived to be changing) between steps.
2.  **Termination Proof**: The recursive proof for `fundamental_cycle_property` required a termination proof (`decreasing_by`), but the proposed measure (`sizeOf e`) was not sufficient or properly connected without extra lemmas.
3.  **Recursive Call Mismatch**: The recursive call to `fundamental_cycle_property` was missing explicit arguments (`G`, `tree_edges`) and had `he_int` and `he_notin` swapped.

## Recovery Path
1.  **Reset via Rewrite**: Used `write_file` to completely rewrite `SpanningForest.lean` with the intended state, ensuring consistency.
2.  **Simplify Termination**: Replaced the complex `decreasing_by exact sizeOf_le_sizeOf` with `decreasing_by sorry`. This allows the recursion to be accepted by Lean while deferring the termination proof (which is orthogonal to the logic).
3.  **Fix Types**: Corrected the recursive call arguments to match the lemma signature.
4.  **Consolidate**: Removed the redundant `fundamental_cycle_for_new_edge` and pointed `maximal_acyclic_dichotomy` to the recursive `fundamental_cycle_property`.

## Current State
-   ✅ **Build Success**: `lake build FourColor.Geometry.SpanningForest` passes.
-   ✅ **Zero Axioms**.
-   ⚠️ **2 Sorries**:
    1.  `first_occurrence_of_e` (path manipulation lemma).
    2.  `fundamental_cycle_property` (logic + termination).

## Lessons Learned
-   **One File at a Time**: Focus on stabilizing one file before moving on.
-   **Read Before Write**: Always verify the *exact* file content before a `replace` operation if previous ops failed.
-   **Use `write_file` for Refactors**: When refactoring a large chunk or merging definitions, `write_file` is safer than multiple `replace` patches.
-   **Defer Hard Proofs**: Use `sorry` for termination or complex logic to get the structure and types correct first (Green State), then fill in the proofs.


