# Four Color Theorem Documentation Index

**Project Root Files:**
- `README.md` - Project overview and setup
- `CLAUDE.md` - Development guidelines and build rules
- `how-to-lean.md` - Lean 4 tactics and formalization patterns
- `STATUS.md` - Current project status
- `DOCS_INDEX.md` - This file

---

## 📁 Documentation Structure

### `docs/spanningforest/` - Spanning Forest Proofs
Current work on proving the spanning forest property for dual graphs.

**Key Files:**
- `SPANNINGFOREST_SUCCESS.md` - Final success summary
- `SPANNINGFOREST_FINAL_STATUS_2025-11-17.md` - Latest status
- `SPANNINGFOREST_MARIO_REALITY_CHECK.md` - Design review
- `GRAPH_THEORY_ATTEMPT_2025-11-19.md` - Graph theory sorry attempts

### `docs/phase-2/` - Face Subtype Refactoring
GPT-5.1's Option A: Face subtype refactoring to eliminate infrastructure sorries.

**Key Files:**
- `PHASE_2_FACE_SUBTYPE_COMPLETE_2025-11-19.md` - **Success summary** ✅
- `PHASE_2_GPT5_STRATEGY_2025-11-19.md` - Original strategy
- `PHASE_2_FINAL_2025-11-19.md` - Final state

### `docs/bridge-proof/` - Bridge Property Proofs
Work on proving the bridge property for planar graphs.

**Key Files:**
- `README_BRIDGE_PROOF.md` - Overview
- `BRIDGE_PROOF_FINAL_STATUS.md` - Final status
- `BRIDGE_PROOF_SUMMARY.md` - Summary

### `docs/lemmas/` - Individual Lemma Work
Specific lemmas from the paper (L4.7, L4.8, etc.)

**Key Files:**
- `L4.7_CLEANUP_COMPLETE.md` - Lemma 4.7 cleanup
- `L4.8_COMPLETE.md` - Lemma 4.8 completion
- `L4.7.2_COMPLETE.md` - Lemma 4.7.2

### `docs/sessions/` - Session Logs
Chronological work sessions from November 2025.

**Organized by date:**
- 2025-11-12: Infrastructure and Theorem 4.10 roadmap
- 2025-11-13: Axiom resolution, face witness
- 2025-11-14: Subtype completion, bite-sized tasks
- 2025-11-15: Grok implementation, final summary
- 2025-11-16: Edge bounds, infrastructure complete

### `docs/archive-2025-11/` - Archived Documentation
Older documentation from November 2025 work sessions.

**Contents:**
- Completion session reports
- Component infrastructure notes
- Critical counterexamples
- GPT-5 proof guidance
- Analysis documents (Grok, Gemini, etc.)

---

## 🎯 Current Focus (2025-11-20)

**Active Work:**
- Spanning Forest: 2 sorries remaining
  - `first_occurrence_of_e` (line 191)
  - `decreasing_by` termination proof (line 408)
- Gemini 3 Pro: Working on termination proof completion

**Build Status:**
- ✅ Zero errors
- ✅ Zero axioms
- ⚠️ 2 sorries (graph theory + termination)
- ✅ Zero linter warnings

---

## 📊 Project Statistics

**Code:**
- Main modules: `FourColor/Geometry/SpanningForest.lean` (554 lines)
- Face subtype refactoring: COMPLETE ✅
- Infrastructure sorries eliminated: 3/5 (60%)

**Documentation:**
- Total .md files: 98 → 4 (in root)
- Organized into 6 categories
- Archive: ~70 historical documents

---

## 🔍 Finding Information

**For current status:**
- Start with `STATUS.md` in project root
- Check `docs/spanningforest/` for latest spanning forest work
- Check `docs/phase-2/` for refactoring achievements

**For historical context:**
- Check `docs/sessions/` for chronological work logs
- Check `docs/archive-2025-11/` for older analysis

**For specific topics:**
- Lemmas → `docs/lemmas/`
- Bridge proofs → `docs/bridge-proof/`
- Spanning forest → `docs/spanningforest/`

---

**Last Updated:** 2025-11-20
**Maintained by:** Claude Code (with Gemini 3 Pro assistance)
