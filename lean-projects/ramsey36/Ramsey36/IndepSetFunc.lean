/-
# Independent Set Search Function (Mathlib-Free)

Pure function definitions for backtracking independent set search.
NO imports beyond Init — only basic types (Nat, Fin, Bool, List).

This file is imported by IndepSub17.lean (which does `by decide` on
sub-problems) so that the kernel evaluation runs without loading
multi-GB Mathlib .olean files into virtual memory.

The completeness proof, structural decomposition lemmas, and bridge
to SimpleGraph all live in IndepSetChecker.lean (which imports Mathlib).
-/

/-- Backtracking search for k-independent sets in a graph on `Fin n`.
    Returns `true` iff an independent set of size `remaining` exists
    among vertices `{start, ..., n-1}` extending `chosen`.
    Recursion depth: `O(n)`, not `O(2^n)`. -/
def hasIndepSetAux (n : Nat) (adj : Fin n → Fin n → Bool)
    (remaining : Nat) (start : Nat) (chosen : List (Fin n)) : Nat → Bool
  | 0 => if remaining = 0 then true else false
  | fuel + 1 =>
    if remaining = 0 then true
    else if h : start < n then
      if n - start < remaining then false
      else
        let v : Fin n := ⟨start, h⟩
        let compatible := chosen.all (fun w => !adj v w)
        if compatible then
          hasIndepSetAux n adj (remaining - 1) (start + 1) (v :: chosen) fuel ||
          hasIndepSetAux n adj remaining (start + 1) chosen fuel
        else
          hasIndepSetAux n adj remaining (start + 1) chosen fuel
    else false

/-- Top-level check. -/
def hasIndepSet (n : Nat) (adj : Fin n → Fin n → Bool) (k : Nat) : Bool :=
  hasIndepSetAux n adj k 0 [] (n + 1)
