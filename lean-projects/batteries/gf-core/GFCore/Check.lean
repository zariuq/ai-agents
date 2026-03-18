/-
# GFCore.Check — Type-check RawTree against GrammarSig

The most important function in the GF-Lean bridge:
  check : GrammarSig → RawTree → Except CheckError CheckedExpr

Verifies that every function name exists in the signature,
arity matches, and child result categories match expected argument categories.
-/

import GFCore.Syntax

namespace GFCore

/-- Check a RawTree against a GrammarSig, producing a CheckedExpr or an error.
    This is the trust boundary: RawTree is untyped wire data from GF;
    CheckedExpr is verified and safe to reason over in Lean. -/
partial def check (sig : GrammarSig) (t : RawTree) : Except CheckError CheckedExpr := do
  let funName := t.funName
  let decl ← match sig.findFun? funName with
    | some d => pure d
    | none   => throw (.unknownFun funName)
  let rawArgs := t.args
  if rawArgs.size != decl.arity then
    throw (.wrongArity funName decl.arity rawArgs.size)
  -- Check cat hint if present
  if let some hint := t.catHint? then
    if hint != decl.resultCat then
      throw (.inconsistentCatHint funName hint decl.resultCat)
  -- Recursively check each argument
  let mut checkedArgs : Array CheckedExpr := #[]
  for i in [:rawArgs.size] do
    let child ← check sig rawArgs[i]!
    let expectedCat := decl.argCats[i]!
    if child.resultCat != expectedCat then
      throw (.catMismatch funName i expectedCat child.resultCat)
    checkedArgs := checkedArgs.push child
  pure (.node decl checkedArgs)

/-- Check a ParseCandidate, returning a checked tree or error. -/
def checkCandidate (sig : GrammarSig) (pc : ParseCandidate) : Except CheckError CheckedExpr :=
  check sig pc.tree

/-- Check multiple ParseCandidates, collecting results. -/
def checkCandidates (sig : GrammarSig) (pcs : Array ParseCandidate)
    : Array (ParseCandidate × Except CheckError CheckedExpr) :=
  pcs.map fun pc => (pc, checkCandidate sig pc)

end GFCore
