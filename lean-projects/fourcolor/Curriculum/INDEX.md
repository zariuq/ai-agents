# Curriculum Index - Quick Reference

## Files

```
Curriculum/
├── README.md           (4.1K) - Master index with all 7 patterns
├── QUICKSTART.md       (5.0K) - How to use the curriculum
├── 01_F2_Parity.lean   (5.5K) - F₂ parity arguments [CRITICAL]
├── 03_Path_XOR.lean    (4.9K) - Path XOR calculus
├── 05_Line_Graph.lean  (3.8K) - Line graph adjacency [EASY]
└── INDEX.md            (this file)
```

## Recommended Reading Order

1. **Start here**: `QUICKSTART.md`
2. **First module**: `05_Line_Graph.lean` (easy, 45 min)
3. **Critical path**: `01_F2_Parity.lean` (hard, 4-5 hours)
4. **Infrastructure**: `03_Path_XOR.lean` (medium, 2-3 hours)

## Pattern → Blocker Mapping

| Pattern | Module | Difficulty | Blockers | Impact |
|---------|--------|------------|----------|--------|
| Line Graph | 5 | ⭐☆☆☆☆ | 2 axioms (Tait) | Quick win |
| F₂ Parity | 1 | ⭐⭐⭐⭐☆ | 1 sorry (KempeAPI) | **CRITICAL** |
| Path XOR | 3 | ⭐⭐⭐☆☆ | 3 axioms (Tait) | Infrastructure |
| Cycle Parity | 2 | ⭐⭐⭐⭐☆ | 2 axioms (Tait) | (Not yet created) |
| Connectivity | 4 | ⭐⭐⭐☆☆ | 1 axiom (Tait) | (Not yet created) |
| Disk Geometry | 6 | TBD | 12 axioms (Disk) | (Needs review) |
| Rotation Systems | 7 | TBD | 5 axioms | (Needs review) |

## Quick Commands

```bash
# Build a curriculum module
lake build Curriculum/01_F2_Parity.lean

# Search for a pattern in mathlib
rg "ZMod 2.*Even" lake-packages/mathlib

# Count remaining sorries
grep -n "sorry\|axiom" FourColor/KempeAPI.lean
grep -n "axiom" FourColor/Tait.lean

# Track your progress
cp QUICKSTART.md MY_PROGRESS.md  # Edit to track exercises
```

## Time Estimates

- **Module 5** (Line Graph): 45 minutes → 2 axioms ✅
- **Module 1** (F₂ Parity): 4-5 hours → 1 sorry ✅ **[CRITICAL]**
- **Module 3** (Path XOR): 2-3 hours → 3 axioms ✅
- **Total (Modules 1,3,5)**: ~7-9 hours → 6 blockers eliminated

## Success Path

```
Start → Module 5 (easy) → Confidence ✅
     → Module 1 (hard) → KempeAPI complete ✅
     → Module 3 (medium) → Tait infrastructure ✅
     → Modules 2,4 → More Tait axioms ✅
     → Modules 6,7 → Foundation review
     → Complete formalization 🎉
```

## Parent Project

This curriculum is part of the **Four Color Theorem Formalization** in Lean 4.

- Main code: `/FourColor/*.lean`
- Documentation: `/*.md` files in project root
- This curriculum: `/Curriculum/*.lean`

---

**Created**: 2025-11-09
**Purpose**: Quick reference for curriculum navigation
**Start here**: Read `QUICKSTART.md`, then try `05_Line_Graph.lean`
