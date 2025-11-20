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

