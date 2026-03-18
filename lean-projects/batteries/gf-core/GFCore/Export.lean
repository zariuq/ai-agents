/-
# GFCore.Export — Erase CheckedExpr back to RawTree

For the linearization direction: Lean produces a CheckedExpr,
erases it to RawTree, serializes to JSON, and GF linearizes it.
-/

import GFCore.Syntax

namespace GFCore

/-- Erase a CheckedExpr back to an untyped RawTree.
    Used for the Lean → GF linearization direction. -/
partial def erase (e : CheckedExpr) : RawTree :=
  .node e.funName (some e.resultCat) (e.args.map erase)

/-- Erase without category hints (minimal JSON output). -/
partial def eraseMinimal (e : CheckedExpr) : RawTree :=
  .node e.funName none (e.args.map eraseMinimal)

-- Round-trip property: check sig (erase e) should succeed and produce
-- a structurally equal CheckedExpr (modulo catHint presence).
-- This follows from check's design but is not proven here.

end GFCore
