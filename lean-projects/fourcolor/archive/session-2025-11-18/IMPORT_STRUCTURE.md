# Import Structure: Why Separate Counterexample File

**Question:** Why is `CounterexampleCaseTwo.lean` a separate file? Can't we just put it in `SpanningForest.lean`?

**Answer:** Circular dependency prevention.

---

## The Problem: Circular Dependencies

If we put the counterexample IN `SpanningForest.lean`:

```
SpanningForest.lean
  ├─ Defines isAcyclic, fundamental_cycle_property, etc.
  └─ Contains counterexample code
     └─ Uses FourCycle structure
```

This would work... **until we try to import it elsewhere**!

```
SomeOtherFile.lean
  imports SpanningForest.lean
    imports ... (heavyweight dependencies)
```

Every file that imports `SpanningForest` would also pull in the counterexample machinery, even though it's only for understanding/documentation.

---

## The Solution: Separate Files

### Current Structure

```
SpanningForest.lean
  ├─ Core definitions (isAcyclic, SpanningForest, etc.)
  ├─ Main proofs (fundamental_cycle_property with 1 sorry)
  └─ Main theorem (exists_spanning_forest)

CounterexampleCaseTwo.lean
  imports SpanningForest.lean  ← One-way dependency!
  ├─ FourCycle structure
  ├─ isAcyclicSimple (simplified version for demo)
  └─ Counterexample proofs
```

### Why This Works

1. **One-way dependency:** Counterexample → SpanningForest ✓
2. **No circular import:** SpanningForest does NOT import Counterexample
3. **Optional import:** Only files that need the counterexample import it
4. **Main proof is clean:** SpanningForest.lean doesn't reference counterexample at all

---

## Import Graph

```
FourColor.lean (root)
  ├─ imports SpanningForest.lean
  │    └─ Main proof code (used by other files)
  │
  └─ imports CounterexampleCaseTwo.lean
       └─ imports SpanningForest.lean (for definitions)
       └─ Counterexample (just for testing/understanding)
```

**Key insight:** The counterexample file imports the main file, not vice versa.

---

## What Gets Used Where

### SpanningForest.lean (Production Code)

**Used by:**
- `Geometry.Disk` - needs `exists_spanning_forest`
- `Kempe.Spanning` - needs `SpanningForest` structure
- Other proof files in the project

**Purpose:** Actual formalization of Lemma 4.7

**Status:** 1 sorry (to be fixed)

### CounterexampleCaseTwo.lean (Documentation/Testing)

**Used by:**
- Nothing! (except FourColor.lean root for testing)

**Purpose:**
- Prove that Case 2 is valid (not impossible)
- Lock in intuition about why the proof works
- Educational/documentation value

**Status:** Has sorries (that's fine, it's just demonstration)

---

## Why We Test The Counterexample

Even though the counterexample isn't used in production:

1. **Verification:** Ensures our mathematical claim is correct
2. **Type-checking:** Makes sure the construction is valid
3. **Documentation:** Keeps the code honest
4. **Confidence:** If counterexample builds, we know it's sound

---

## Adding New Files

If you create a new helper file:

### If it's USED by production code:
```lean
-- NewHelper.lean
import FourColor.Geometry.SpanningForest

-- SpanningForest.lean
import FourColor.Geometry.NewHelper  -- ❌ CIRCULAR!
```

**Solution:** Put helpers BEFORE they're needed in import hierarchy.

### If it's just for DOCUMENTATION:
```lean
-- NewDoc.lean
import FourColor.Geometry.SpanningForest  -- ✓ OK

-- SpanningForest.lean
-- (doesn't import NewDoc)  -- ✓ OK
```

**Solution:** One-way dependency, like counterexample.

---

## TL;DR

**Q:** Why separate files?
**A:** Prevent circular dependencies.

**Q:** Where does counterexample fit?
**A:** It imports SpanningForest, not vice versa.

**Q:** Is this pattern common?
**A:** Yes! Examples:
- Main proof file
- Separate counterexample/test files
- Separate documentation files
- All import the main file, never the reverse

**Q:** Should I import the counterexample in my proof?
**A:** NO! The counterexample is for understanding. Your proof should never reference it.

---

**Bottom line:**
- `SpanningForest.lean` = production code (imported by other proofs)
- `CounterexampleCaseTwo.lean` = documentation (imports SpanningForest)
- One-way dependency prevents circular imports
- Both can be tested independently
