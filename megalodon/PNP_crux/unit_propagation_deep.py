#!/usr/bin/env python3
"""
UNIT PROPAGATION DEEP DIVE

Critical test: Can unit propagation on local tree-like neighborhoods
correctly determine the planted assignment WITHOUT knowing it?

This is the make-or-break test for Goertzel's proof.
"""

import random
from typing import List, Tuple, Dict, Set, Optional
from collections import deque

def generate_planted_3sat(n: int, m: int, seed: int = 42):
    """Generate a planted 3-SAT instance."""
    random.seed(seed)
    planted = [random.choice([True, False]) for _ in range(n)]
    clauses = []
    signs = []
    for _ in range(m):
        vars = tuple(sorted(random.sample(range(n), 3)))
        while True:
            s = tuple(random.choice([True, False]) for _ in range(3))
            satisfied = any(
                (planted[vars[j]] if s[j] else not planted[vars[j]])
                for j in range(3)
            )
            if satisfied:
                break
        clauses.append(vars)
        signs.append(s)
    return planted, clauses, signs


def build_local_neighborhood(var_i: int, clauses: List, signs: List, depth: int) -> Dict:
    """Build local factor graph around variable i."""
    local_clauses = []
    local_vars = {var_i}
    frontier = {var_i}

    for d in range(depth):
        new_frontier = set()
        for c_idx, clause in enumerate(clauses):
            if any(v in frontier for v in clause):
                if c_idx not in [lc[0] for lc in local_clauses]:
                    local_clauses.append((c_idx, clause, signs[c_idx]))
                    for v in clause:
                        if v not in local_vars:
                            new_frontier.add(v)
                            local_vars.add(v)
        frontier = new_frontier
        if not frontier:
            break

    return {
        'center': var_i,
        'vars': local_vars,
        'clauses': local_clauses,
        'depth': depth
    }


def unit_propagation_pure(local_fg: Dict) -> Tuple[Dict[int, bool], bool, str]:
    """
    Pure unit propagation WITHOUT any initial assignments.

    Returns: (assignments, success, reason)
    - assignments: dict of variable -> value determined by UP
    - success: True if no conflict
    - reason: explanation
    """

    vars = local_fg['vars']
    clauses = local_fg['clauses']

    # Track assignments and clause states
    assignments = {}  # var -> bool

    # Convert clauses to working format
    # Each clause: list of (var, sign) tuples, where sign=True means positive literal
    working_clauses = []
    for c_idx, clause, signs in clauses:
        lits = [(clause[j], signs[j]) for j in range(3)]
        working_clauses.append(lits)

    changed = True
    while changed:
        changed = False

        for clause_lits in working_clauses:
            # Count unassigned and check satisfaction
            unassigned = []
            satisfied = False

            for var, sign in clause_lits:
                if var in assignments:
                    # Literal value: var_value XOR (not sign)
                    lit_val = assignments[var] if sign else not assignments[var]
                    if lit_val:
                        satisfied = True
                        break
                else:
                    unassigned.append((var, sign))

            if satisfied:
                continue

            if len(unassigned) == 0:
                # All assigned but not satisfied = CONFLICT
                return assignments, False, "Conflict: all literals false"

            if len(unassigned) == 1:
                # Unit clause! Must assign to satisfy
                var, sign = unassigned[0]
                # Need literal to be true: if sign=True, var=True; if sign=False, var=False
                required_val = sign

                if var in assignments:
                    if assignments[var] != required_val:
                        return assignments, False, f"Conflict at var {var}"
                else:
                    assignments[var] = required_val
                    changed = True

    return assignments, True, "No conflict"


def unit_propagation_with_boundary(local_fg: Dict, boundary_values: Dict[int, bool]) -> Tuple[Dict[int, bool], bool]:
    """
    Unit propagation with known boundary values.

    This simulates having oracle access to boundary variable values.
    """

    clauses = local_fg['clauses']
    assignments = dict(boundary_values)  # Start with boundary

    working_clauses = []
    for c_idx, clause, signs in clauses:
        lits = [(clause[j], signs[j]) for j in range(3)]
        working_clauses.append(lits)

    changed = True
    iterations = 0
    max_iter = 100

    while changed and iterations < max_iter:
        changed = False
        iterations += 1

        for clause_lits in working_clauses:
            unassigned = []
            satisfied = False

            for var, sign in clause_lits:
                if var in assignments:
                    lit_val = assignments[var] if sign else not assignments[var]
                    if lit_val:
                        satisfied = True
                        break
                else:
                    unassigned.append((var, sign))

            if satisfied:
                continue

            if len(unassigned) == 0:
                return assignments, False  # Conflict

            if len(unassigned) == 1:
                var, sign = unassigned[0]
                required_val = sign
                if var in assignments and assignments[var] != required_val:
                    return assignments, False
                assignments[var] = required_val
                changed = True

    return assignments, True


def test_pure_up(n: int, alpha: float, depth: int, num_trials: int = 5):
    """Test pure unit propagation (no initial assignments)."""

    m = int(alpha * n)

    total_tests = 0
    determined_center = 0
    correct_center = 0
    total_determined = 0
    total_vars = 0

    for trial in range(num_trials):
        planted, clauses, signs = generate_planted_3sat(n, m, seed=trial * 1000)
        test_vars = random.sample(range(n), min(10, n))

        for var_i in test_vars:
            local_fg = build_local_neighborhood(var_i, clauses, signs, depth)
            assignments, success, reason = unit_propagation_pure(local_fg)

            total_tests += 1
            total_vars += len(local_fg['vars'])
            total_determined += len(assignments)

            if var_i in assignments:
                determined_center += 1
                if assignments[var_i] == planted[var_i]:
                    correct_center += 1

    return {
        'total_tests': total_tests,
        'determined_center': determined_center,
        'correct_center': correct_center,
        'det_rate': determined_center / total_tests if total_tests > 0 else 0,
        'correct_rate': correct_center / determined_center if determined_center > 0 else 0,
        'avg_determined': total_determined / total_tests if total_tests > 0 else 0,
        'avg_vars': total_vars / total_tests if total_tests > 0 else 0,
    }


def test_boundary_up(n: int, alpha: float, depth: int, num_trials: int = 5):
    """Test UP with boundary values from planted assignment."""

    m = int(alpha * n)

    total_tests = 0
    determined_center = 0
    correct_center = 0

    for trial in range(num_trials):
        planted, clauses, signs = generate_planted_3sat(n, m, seed=trial * 1000)
        test_vars = random.sample(range(n), min(10, n))

        for var_i in test_vars:
            local_fg = build_local_neighborhood(var_i, clauses, signs, depth)

            # Get boundary vars (vars at max depth, not center)
            center_clauses = set()
            for c_idx, clause, _ in local_fg['clauses']:
                if var_i in clause:
                    center_clauses.add(c_idx)

            # Boundary = vars not in center's direct clauses
            boundary_vars = set()
            for v in local_fg['vars']:
                if v == var_i:
                    continue
                is_boundary = True
                for c_idx, clause, _ in local_fg['clauses']:
                    if v in clause and c_idx in center_clauses:
                        is_boundary = False
                        break
                if is_boundary:
                    boundary_vars.add(v)

            # Give UP the planted values for boundary
            boundary_values = {v: planted[v] for v in boundary_vars}

            assignments, success = unit_propagation_with_boundary(local_fg, boundary_values)

            total_tests += 1
            if var_i in assignments:
                determined_center += 1
                if assignments[var_i] == planted[var_i]:
                    correct_center += 1

    return {
        'total_tests': total_tests,
        'determined_center': determined_center,
        'correct_center': correct_center,
        'det_rate': determined_center / total_tests if total_tests > 0 else 0,
        'correct_rate': correct_center / determined_center if determined_center > 0 else 0,
    }


def analyze_up_failure_modes(n: int, alpha: float, depth: int, seed: int = 42):
    """Analyze why UP fails in specific cases."""

    m = int(alpha * n)
    planted, clauses, signs = generate_planted_3sat(n, m, seed)

    failure_reasons = {
        'no_unit_clauses': 0,
        'center_not_reached': 0,
        'wrong_value': 0,
        'conflict': 0,
        'success': 0,
    }

    for var_i in range(min(20, n)):
        local_fg = build_local_neighborhood(var_i, clauses, signs, depth)

        # Check if any clause is initially unit (has only 1 var in local neighborhood)
        has_unit = False
        for c_idx, clause, signs_c in local_fg['clauses']:
            local_count = sum(1 for v in clause if v in local_fg['vars'])
            if local_count == 1:
                has_unit = True
                break

        assignments, success, reason = unit_propagation_pure(local_fg)

        if not success:
            failure_reasons['conflict'] += 1
        elif var_i not in assignments:
            if not has_unit:
                failure_reasons['no_unit_clauses'] += 1
            else:
                failure_reasons['center_not_reached'] += 1
        elif assignments[var_i] != planted[var_i]:
            failure_reasons['wrong_value'] += 1
        else:
            failure_reasons['success'] += 1

    return failure_reasons


def main():
    print("=" * 70)
    print("UNIT PROPAGATION DEEP DIVE")
    print("Testing if UP can determine planted assignment")
    print("=" * 70)
    print()

    # Test 1: Pure UP (no initial knowledge)
    print("TEST 1: PURE UNIT PROPAGATION")
    print("-" * 50)
    print("(No initial assignments - can UP determine anything?)")
    print()

    configs = [
        (50, 2.0, 2),
        (50, 2.0, 3),
        (50, 3.0, 2),
        (50, 3.0, 3),
        (100, 2.5, 3),
    ]

    print(f"{'n':>6} {'α':>6} {'depth':>6} {'det%':>10} {'correct%':>10} {'avg_det':>10}")
    print("-" * 60)

    pure_results = []
    for n, alpha, depth in configs:
        result = test_pure_up(n, alpha, depth, num_trials=3)
        det_pct = result['det_rate'] * 100
        corr_pct = result['correct_rate'] * 100
        pure_results.append((n, alpha, depth, det_pct, corr_pct))
        print(f"{n:>6} {alpha:>6.1f} {depth:>6} {det_pct:>9.1f}% {corr_pct:>9.1f}% {result['avg_determined']:>10.1f}")

    print()
    avg_det = sum(r[3] for r in pure_results) / len(pure_results)
    print(f"Average determination rate: {avg_det:.1f}%")
    print()

    if avg_det < 5:
        print("⚠ CRITICAL: Pure UP determines almost NOTHING!")
        print("  UP needs initial assignments to start propagation.")
        print()

    # Test 2: UP with boundary knowledge
    print("TEST 2: UP WITH BOUNDARY VALUES (Oracle)")
    print("-" * 50)
    print("(Given boundary values from planted - can UP reach center?)")
    print()

    print(f"{'n':>6} {'α':>6} {'depth':>6} {'det%':>10} {'correct%':>10}")
    print("-" * 50)

    boundary_results = []
    for n, alpha, depth in configs:
        result = test_boundary_up(n, alpha, depth, num_trials=3)
        det_pct = result['det_rate'] * 100
        corr_pct = result['correct_rate'] * 100
        boundary_results.append((n, alpha, depth, det_pct, corr_pct))
        print(f"{n:>6} {alpha:>6.1f} {depth:>6} {det_pct:>9.1f}% {corr_pct:>9.1f}%")

    print()
    avg_det_boundary = sum(r[3] for r in boundary_results) / len(boundary_results)
    avg_corr_boundary = sum(r[4] for r in boundary_results if r[3] > 0) / max(1, sum(1 for r in boundary_results if r[3] > 0))
    print(f"Average determination rate: {avg_det_boundary:.1f}%")
    print(f"Average correctness (when determined): {avg_corr_boundary:.1f}%")
    print()

    # Test 3: Failure mode analysis
    print("TEST 3: FAILURE MODE ANALYSIS")
    print("-" * 50)

    reasons = analyze_up_failure_modes(100, 2.5, 3)
    total = sum(reasons.values())
    print(f"Results for n=100, α=2.5, depth=3:")
    for reason, count in sorted(reasons.items(), key=lambda x: -x[1]):
        print(f"  {reason}: {count} ({100*count/total:.1f}%)")

    print()
    print("=" * 70)
    print("CRITICAL ANALYSIS")
    print("=" * 70)
    print()

    if avg_det < 10:
        print("FINDING: Pure UP determines < 10% of center variables")
        print()
        print("ROOT CAUSE:")
        print("  - UP needs UNIT CLAUSES to start (clauses with 1 unassigned var)")
        print("  - In a fresh formula, ALL clauses have 3 unassigned vars")
        print("  - UP cannot start without external information!")
        print()
        print("IMPLICATION FOR PROOF:")
        print("  - 'GE on VV constraints' CANNOT mean pure unit propagation")
        print("  - The decoder MUST use some other source of information")
        print("  - Possibilities:")
        print("    1. BP marginals guide initial decisions")
        print("    2. Random guessing + backtracking (DPLL)")
        print("    3. Some other constraint formulation")
        print()

    if avg_det_boundary > 50:
        print("FINDING: UP WITH BOUNDARY VALUES works ({:.1f}%)".format(avg_det_boundary))
        print()
        print("  This confirms: IF we know boundary values, UP can propagate inward.")
        print("  BUT: We don't have an oracle for boundary values!")
        print()

    # The key question
    print("=" * 70)
    print("THE KEY QUESTION")
    print("=" * 70)
    print()
    print("How does the decoder get INITIAL information to start propagation?")
    print()
    print("Option A: BP provides soft evidence")
    print("  - BP marginals give P(var=1)")
    print("  - Threshold at 0.5 to get hard assignments")
    print("  - This is what we tested earlier (81% accuracy)")
    print()
    print("Option B: Some special structure in planted SAT")
    print("  - Maybe planted instances have detectable features")
    print("  - This would be a new algorithmic claim")
    print()
    print("Option C: The proof has a GAP")
    print("  - 'GE on VV constraints' is undefined/unclear")
    print("  - No concrete decoder construction is given")
    print()

    # Verdict
    print("=" * 70)
    print("VERDICT")
    print("=" * 70)
    print()

    if avg_det < 10:
        print("❌ UNIT PROPAGATION ALONE CANNOT BUILD THE DECODER")
        print()
        print("The proof relies on 'GE on VV constraints' but:")
        print("  1. XOR linear system: FAILS (0% consistency)")
        print("  2. Pure UP: FAILS (can't start without oracle)")
        print("  3. BP-guided: WORKS (~81%) but is PROBABILISTIC")
        print()
        print("If 'GE' must be deterministic, the proof has a CRITICAL GAP.")
        print("If 'GE' can use BP, we need to verify BP gives EXACT answers.")

        return 1
    else:
        print("✓ Unit propagation shows some promise")
        return 0


if __name__ == "__main__":
    exit(main())
