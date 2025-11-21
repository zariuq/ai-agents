/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Main Theorem: R(3,6) = 18

This file contains the main result combining both bounds.
-/

import Ramsey36.Basic
import Ramsey36.Critical17

open SimpleGraph

/-! ## The Bridge Theorem -/

/-- **Main Result**: The Ramsey number R(3,6) equals 18.

    This combines two results:
    - Lower bound: 18 ≤ R(3,6) (from Critical17, using nonemptiness)
    - Upper bound: R(3,6) ≤ 18 (from Basic)
-/
theorem ramsey_three_six : ramseyNumber 3 6 = 18 := by
  apply Nat.le_antisymm
  · -- Upper bound: R(3,6) ≤ 18
    exact ramsey_three_six_upper
  · -- Lower bound: 18 ≤ R(3,6)
    -- We use the lower bound logic which requires knowing the set is nonempty
    apply ramsey_three_six_ge_18_of_nonempty
    -- Nonemptiness is provided by the upper bound (18 has the property)
    exact ramseySet_3_6_nonempty