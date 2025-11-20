# Curriculum Quick Start Guide

## Goal
Learn proof patterns systematically to eliminate ALL sorries/axioms in the Four Color Theorem formalization.

## Recommended Path

### Phase 1: Quick Wins (1-2 hours)
**Goal**: Build confidence, eliminate easy axioms

1. **Module 5: Line Graph** (⭐☆☆☆☆)
   - Exercises: 30 minutes
   - Application: 15 minutes
   - **Unlocks**: 2 axioms in Tait.lean

**Why start here**: Pure definitional manipulation, instant gratification

### Phase 2: Critical Path (3-5 hours)
**Goal**: Unblock KempeAPI completely

2. **Module 1: F₂ Parity** (⭐⭐⭐⭐☆)
   - Exercises: 2-3 hours
   - Application: 1 hour
   - **Unlocks**: THE blocker in KempeAPI

**Why next**: This is blocking everything downstream. Hardest but highest value.

### Phase 3: Tait Infrastructure (4-6 hours)
**Goal**: Eliminate Tait.lean axioms

3. **Module 3: Path XOR** (⭐⭐⭐☆☆)
   - Exercises: 2 hours
   - Application: 1 hour
   - **Unlocks**: 3 axioms in Tait.lean

4. **Module 2: Cycle Parity** (⭐⭐⭐⭐☆)
   - Exercises: 2-3 hours
   - Application: 1-2 hours
   - **Unlocks**: 2 axioms in Tait.lean

5. **Module 4: Connectivity** (⭐⭐⭐☆☆)
   - Exercises: 1-2 hours
   - Application: 1 hour
   - **Unlocks**: 1 axiom in Tait.lean

### Phase 4: Geometry Foundation (Review needed)
**Goal**: Assess which axioms are truly foundational

6-7. **Modules 6-7: Disk & Rotation Systems**
   - Status: Need to review if these should be axioms or proven
   - ~17 axioms total

## How to Work Through a Module

### Step 1: Read the Module
- Understand the pattern
- See why it matters
- Note the blockers it eliminates

### Step 2: Solve Exercises
- Start with Exercise 1 (warmup)
- Use hints if stuck
- Search mathlib for similar proofs (use `rg` commands in hints)
- **Don't skip ahead** - each builds on previous

### Step 3: Check Your Solutions
- Run `lake build Curriculum/XX_ModuleName.lean`
- Fix any errors
- Refine your proof (make it cleaner)

### Step 4: Apply to Real Code
- Find the actual axiom/sorry in the main codebase
- Copy your solution pattern
- Adapt to the specific context
- **Remove the axiom/sorry**, replace with proof

### Step 5: Verify
```bash
lake build FourColor.Tait  # or whichever file you modified
grep -n "axiom\|sorry" FourColor/TheFile.lean  # count should go down!
```

## Pro Tips

### When Stuck on an Exercise
1. **Read the hint** - they're specific and helpful
2. **Search mathlib**: `rg "relevant_lemma_name" lake-packages/mathlib`
3. **Ask for the answer** - the goal is learning, not suffering
4. **Move to next exercise** - come back later with fresh eyes

### When Stuck on Application
1. **Compare**: Your minimal example vs. actual code - what's different?
2. **Types matter**: Make sure hypotheses match exactly
3. **Use `sorry` strategically**: Fill in the easy parts, focus on the hard part
4. **Build incrementally**: Get it compiling with sorries, then fill them

### Time Management
- **Don't binge**: 1-2 hours per session max
- **Take breaks**: After each exercise
- **Switch modules**: If stuck on one, try another
- **Celebrate wins**: Each axiom eliminated is real progress!

## Tracking Progress

Create a file `Curriculum/MY_PROGRESS.md`:

```markdown
# My Progress

## Module 1: F₂ Parity
- [ ] Exercise 1a
- [ ] Exercise 2a
- [ ] Exercise 3a
- [ ] Exercise 3b
- [ ] Exercise 4
- [ ] Applied to KempeAPI.lean:320

## Module 5: Line Graph
- [x] Exercise 1a ✅
- [x] Exercise 2a ✅
- [x] Applied to Tait.lean:269 ✅
- [x] Applied to Tait.lean:278 ✅

... etc
```

## Success Metrics

**After Phase 1**: 2 fewer axioms, confidence boosted
**After Phase 2**: KempeAPI complete, can prove downstream theorems
**After Phase 3**: Tait.lean clean, graph theory solid
**After Phase 4**: Full assessment of foundational axioms

## Help Resources

### Where to Find Answers
1. **Mathlib docs**: https://leanprover-community.github.io/mathlib4_docs/
2. **Lean Zulip**: https://leanprover.zulipchat.com/
3. **This curriculum**: Check solutions in other modules for similar patterns

### When to Ask for Help
- After trying for 30+ minutes
- When you don't understand what the exercise is asking
- When your proof works but you think it's ugly

### How to Ask
Include:
1. Which exercise you're on
2. What you've tried
3. The error message or where you're stuck
4. Your current attempt (code)

## Expected Outcomes

**Week 1**: Modules 5 and 1 complete (easy + critical)
**Week 2**: Modules 3 and 2 complete (Tait infrastructure)
**Week 3**: Module 4 complete, review Modules 6-7
**Week 4**: All applicable axioms eliminated, only foundational ones remain

**Total time investment**: ~20-30 hours over 4 weeks
**Return**: Complete understanding of core proof patterns, zero unproven statements in main theorems

---

**Remember**: The goal isn't to memorize solutions, it's to internalize PATTERNS. After Module 1, you'll recognize F₂ arguments everywhere. After Module 3, path composition will be second nature.

**Start today with Module 5** - 45 minutes to your first axioms eliminated!
