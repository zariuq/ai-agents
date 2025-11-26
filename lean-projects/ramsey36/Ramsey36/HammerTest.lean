import Hammer
import Mathlib.Tactic
import Ramsey36.Basic

open SimpleGraph

-- Test 1: Simple tautology
example : True := by
  hammer

-- Test 2: Simple arithmetic
example (n : Nat) : n + 0 = n := by
  hammer

-- Test 3: Symmetry of simple graph adjacency
example {V : Type*} (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : G.Adj v u := by
  hammer
