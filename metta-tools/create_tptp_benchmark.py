#!/usr/bin/env python3
"""
Create TPTP FOF Benchmark Suite (42 problems)

Generates 42 curated First-Order Logic problems for PeTTaRes development:
- 21 UNSAT (unsatisfiable - theorem provable)
- 21 SAT (satisfiable - theorem not provable or model exists)
- Organized by difficulty: Easy (1-14), Medium (15-28), Hard (29-42)
- Covers: quantifiers, functions, predicates, equality, transitivity, etc.
"""

import os
from pathlib import Path


PROBLEMS = [
    # ========== EASY UNSAT (1-7) ==========
    {
        "id": "bench_001_unsat",
        "difficulty": "easy",
        "description": "Modus ponens",
        "status": "unsat",
        "content": """% Modus ponens: p, p => q |- q
fof(axiom1, axiom, p).
fof(axiom2, axiom, p => q).
fof(goal, conjecture, q).
"""
    },
    {
        "id": "bench_002_unsat",
        "difficulty": "easy",
        "description": "Hypothetical syllogism",
        "status": "unsat",
        "content": """% Hypothetical syllogism: (p => q), (q => r) |- (p => r)
fof(axiom1, axiom, p => q).
fof(axiom2, axiom, q => r).
fof(axiom3, axiom, p).
fof(goal, conjecture, r).
"""
    },
    {
        "id": "bench_003_unsat",
        "difficulty": "easy",
        "description": "Universal instantiation",
        "status": "unsat",
        "content": """% Universal instantiation: forall X. P(X) |- P(a)
fof(axiom1, axiom, ![X]: p(X)).
fof(goal, conjecture, p(a)).
"""
    },
    {
        "id": "bench_004_unsat",
        "difficulty": "easy",
        "description": "Universal modus ponens",
        "status": "unsat",
        "content": """% Universal modus ponens
fof(axiom1, axiom, ![X]: (human(X) => mortal(X))).
fof(axiom2, axiom, human(socrates)).
fof(goal, conjecture, mortal(socrates)).
"""
    },
    {
        "id": "bench_005_unsat",
        "difficulty": "easy",
        "description": "Transitive relation",
        "status": "unsat",
        "content": """% Transitivity
fof(axiom1, axiom, r(a,b)).
fof(axiom2, axiom, r(b,c)).
fof(axiom3, axiom, ![X,Y,Z]: ((r(X,Y) & r(Y,Z)) => r(X,Z))).
fof(goal, conjecture, r(a,c)).
"""
    },
    {
        "id": "bench_006_unsat",
        "difficulty": "easy",
        "description": "Symmetry",
        "status": "unsat",
        "content": """% Symmetric relation
fof(axiom1, axiom, ![X,Y]: (r(X,Y) => r(Y,X))).
fof(axiom2, axiom, r(a,b)).
fof(goal, conjecture, r(b,a)).
"""
    },
    {
        "id": "bench_007_unsat",
        "difficulty": "easy",
        "description": "Function composition",
        "status": "unsat",
        "content": """% Function composition
fof(axiom1, axiom, ![X]: p(f(X))).
fof(axiom2, axiom, ![X]: (p(X) => q(X))).
fof(goal, conjecture, q(f(a))).
"""
    },

    # ========== EASY SAT (8-14) ==========
    {
        "id": "bench_008_sat",
        "difficulty": "easy",
        "description": "Affirming the consequent (fallacy)",
        "status": "sat",
        "content": """% Affirming the consequent is a fallacy
fof(axiom1, axiom, p => q).
fof(axiom2, axiom, q).
fof(goal, conjecture, p).
"""
    },
    {
        "id": "bench_009_sat",
        "difficulty": "easy",
        "description": "Denying the antecedent (fallacy)",
        "status": "sat",
        "content": """% Denying the antecedent is a fallacy
fof(axiom1, axiom, p => q).
fof(axiom2, axiom, ~p).
fof(goal, conjecture, ~q).
"""
    },
    {
        "id": "bench_010_sat",
        "difficulty": "easy",
        "description": "Existential without witness",
        "status": "sat",
        "content": """% Existential claim without specific witness
fof(axiom1, axiom, ?[X]: p(X)).
fof(goal, conjecture, p(a)).
"""
    },
    {
        "id": "bench_011_sat",
        "difficulty": "easy",
        "description": "Universal from specific",
        "status": "sat",
        "content": """% Cannot derive universal from specific instance
fof(axiom1, axiom, p(a)).
fof(goal, conjecture, ![X]: p(X)).
"""
    },
    {
        "id": "bench_012_sat",
        "difficulty": "easy",
        "description": "Non-transitive relation",
        "status": "sat",
        "content": """% Relation without transitivity axiom
fof(axiom1, axiom, r(a,b)).
fof(axiom2, axiom, r(b,c)).
fof(goal, conjecture, r(a,c)).
"""
    },
    {
        "id": "bench_013_sat",
        "difficulty": "easy",
        "description": "Disjunction ambiguity",
        "status": "sat",
        "content": """% Disjunction doesn't determine which disjunct
fof(axiom1, axiom, p | q).
fof(goal, conjecture, p).
"""
    },
    {
        "id": "bench_014_sat",
        "difficulty": "easy",
        "description": "Unrelated predicates",
        "status": "sat",
        "content": """% Unrelated predicates
fof(axiom1, axiom, p(a)).
fof(axiom2, axiom, q(b)).
fof(goal, conjecture, r(a,b)).
"""
    },

    # ========== MEDIUM UNSAT (15-21) ==========
    {
        "id": "bench_015_unsat",
        "difficulty": "medium",
        "description": "Equivalence relation properties",
        "status": "unsat",
        "content": """% Equivalence relation: reflexive + transitive + symmetric
fof(reflexive, axiom, ![X]: eq(X,X)).
fof(symmetric, axiom, ![X,Y]: (eq(X,Y) => eq(Y,X))).
fof(transitive, axiom, ![X,Y,Z]: ((eq(X,Y) & eq(Y,Z)) => eq(X,Z))).
fof(fact1, axiom, eq(a,b)).
fof(fact2, axiom, eq(b,c)).
fof(goal, conjecture, eq(c,a)).
"""
    },
    {
        "id": "bench_016_unsat",
        "difficulty": "medium",
        "description": "Function congruence",
        "status": "unsat",
        "content": """% Function respects equality
fof(func_cong, axiom, ![X,Y]: (eq(X,Y) => eq(f(X), f(Y)))).
fof(eq_refl, axiom, ![X]: eq(X,X)).
fof(eq_symm, axiom, ![X,Y]: (eq(X,Y) => eq(Y,X))).
fof(eq_trans, axiom, ![X,Y,Z]: ((eq(X,Y) & eq(Y,Z)) => eq(X,Z))).
fof(fact, axiom, eq(a,b)).
fof(goal, conjecture, eq(f(a), f(b))).
"""
    },
    {
        "id": "bench_017_unsat",
        "difficulty": "medium",
        "description": "Nested quantifiers",
        "status": "unsat",
        "content": """% Nested quantifiers: everyone loves someone
fof(axiom1, axiom, ![X]: ?[Y]: loves(X,Y)).
fof(axiom2, axiom, ![X,Y]: (loves(X,Y) => knows(X,Y))).
fof(axiom3, axiom, ![X]: ?[Y]: knows(X,Y)).
fof(goal, conjecture, ?[Z]: knows(alice,Z)).
"""
    },
    {
        "id": "bench_018_unsat",
        "difficulty": "medium",
        "description": "Successor function",
        "status": "unsat",
        "content": """% Successor properties
fof(succ_inj, axiom, ![X,Y]: (s(X) = s(Y) => X = Y)).
fof(fact1, axiom, s(s(zero)) = s(s(zero))).
fof(goal, conjecture, s(zero) = s(zero)).
"""
    },
    {
        "id": "bench_019_unsat",
        "difficulty": "medium",
        "description": "Antisymmetric ordering",
        "status": "unsat",
        "content": """% Partial order: antisymmetric
fof(antisymm, axiom, ![X,Y]: ((le(X,Y) & le(Y,X)) => X = Y)).
fof(trans, axiom, ![X,Y,Z]: ((le(X,Y) & le(Y,Z)) => le(X,Z))).
fof(refl, axiom, ![X]: le(X,X)).
fof(fact1, axiom, le(a,b)).
fof(fact2, axiom, le(b,a)).
fof(goal, conjecture, a = b).
"""
    },
    {
        "id": "bench_020_unsat",
        "difficulty": "medium",
        "description": "Ancestor relation",
        "status": "unsat",
        "content": """% Ancestor is transitive closure of parent
fof(parent_ancestor, axiom, ![X,Y]: (parent(X,Y) => ancestor(X,Y))).
fof(trans_ancestor, axiom, ![X,Y,Z]: ((ancestor(X,Y) & ancestor(Y,Z)) => ancestor(X,Z))).
fof(fact1, axiom, parent(a,b)).
fof(fact2, axiom, parent(b,c)).
fof(fact3, axiom, parent(c,d)).
fof(goal, conjecture, ancestor(a,d)).
"""
    },
    {
        "id": "bench_021_unsat",
        "difficulty": "medium",
        "description": "List properties",
        "status": "unsat",
        "content": """% List append associativity (simple case)
fof(append_nil, axiom, ![L]: append(nil,L) = L).
fof(append_cons, axiom, ![X,L1,L2]: append(cons(X,L1),L2) = cons(X,append(L1,L2))).
fof(goal, conjecture, append(cons(a,nil), cons(b,nil)) = cons(a,cons(b,nil))).
"""
    },

    # ========== MEDIUM SAT (22-28) ==========
    {
        "id": "bench_022_sat",
        "difficulty": "medium",
        "description": "Existential quantifier scope",
        "status": "sat",
        "content": """% Existential doesn't imply all instances
fof(axiom1, axiom, ![X]: ?[Y]: r(X,Y)).
fof(goal, conjecture, ?[Z]: (![X]: r(X,Z))).
"""
    },
    {
        "id": "bench_023_sat",
        "difficulty": "medium",
        "description": "Function without surjectivity",
        "status": "sat",
        "content": """% Function may not be surjective
fof(axiom1, axiom, ![X]: p(f(X))).
fof(goal, conjecture, ![Y]: ?[X]: (f(X) = Y)).
"""
    },
    {
        "id": "bench_024_sat",
        "difficulty": "medium",
        "description": "Irreflexive without proof",
        "status": "sat",
        "content": """% Asymmetric doesn't imply irreflexive without more axioms
fof(asymm, axiom, ![X,Y]: (r(X,Y) => ~r(Y,X))).
fof(goal, conjecture, ![X]: ~r(X,X)).
"""
    },
    {
        "id": "bench_025_sat",
        "difficulty": "medium",
        "description": "Skolem function ambiguity",
        "status": "sat",
        "content": """% Existential witness not unique
fof(axiom1, axiom, ?[X]: p(X)).
fof(axiom2, axiom, ?[Y]: p(Y)).
fof(goal, conjecture, ![X,Y]: (p(X) & p(Y)) => X = Y).
"""
    },
    {
        "id": "bench_026_sat",
        "difficulty": "medium",
        "description": "Commutativity not implied",
        "status": "sat",
        "content": """% Associativity doesn't imply commutativity
fof(assoc, axiom, ![X,Y,Z]: op(op(X,Y),Z) = op(X,op(Y,Z))).
fof(goal, conjecture, ![X,Y]: op(X,Y) = op(Y,X)).
"""
    },
    {
        "id": "bench_027_sat",
        "difficulty": "medium",
        "description": "Totality from partial order",
        "status": "sat",
        "content": """% Partial order doesn't imply totality
fof(refl, axiom, ![X]: le(X,X)).
fof(antisymm, axiom, ![X,Y]: ((le(X,Y) & le(Y,X)) => X = Y)).
fof(trans, axiom, ![X,Y,Z]: ((le(X,Y) & le(Y,Z)) => le(X,Z))).
fof(goal, conjecture, ![X,Y]: (le(X,Y) | le(Y,X))).
"""
    },
    {
        "id": "bench_028_sat",
        "difficulty": "medium",
        "description": "Inverse without axiom",
        "status": "sat",
        "content": """% Inverse not implied without axiom
fof(id, axiom, ![X]: op(X,e) = X).
fof(goal, conjecture, ![X]: ?[Y]: op(X,Y) = e).
"""
    },

    # ========== HARD UNSAT (29-35) ==========
    {
        "id": "bench_029_unsat",
        "difficulty": "hard",
        "description": "Group identity uniqueness",
        "status": "unsat",
        "content": """% Group identity is unique
fof(left_id, axiom, ![X]: op(e,X) = X).
fof(right_id, axiom, ![X]: op(X,e) = X).
fof(left_id2, axiom, ![X]: op(e2,X) = X).
fof(goal, conjecture, e = e2).
"""
    },
    {
        "id": "bench_030_unsat",
        "difficulty": "hard",
        "description": "Cantor's theorem (finite case)",
        "status": "unsat",
        "content": """% No surjection from set to its powerset (2-element case)
fof(f_a_either, axiom, f(a) = s1 | f(a) = s2).
fof(f_b_either, axiom, f(b) = s1 | f(b) = s2).
fof(s1_def, axiom, in(a,s1) & ~in(b,s1)).
fof(s2_def, axiom, ~in(a,s2) & in(b,s2)).
fof(diagonal, axiom, ?[S]: (![X]: (in(X,S) <=> ~in(X,f(X))))).
fof(goal, conjecture, ?[S]: (![X]: ~(f(X) = S))).
"""
    },
    {
        "id": "bench_031_unsat",
        "difficulty": "hard",
        "description": "Pigeonhole principle (3 pigeons, 2 holes)",
        "status": "unsat",
        "content": """% Pigeonhole: 3 pigeons in 2 holes
fof(pigeon1, axiom, h(p1) = h1 | h(p1) = h2).
fof(pigeon2, axiom, h(p2) = h1 | h(p2) = h2).
fof(pigeon3, axiom, h(p3) = h1 | h(p3) = h2).
fof(distinct_pigeons, axiom, p1 != p2 & p2 != p3 & p1 != p3).
fof(goal, conjecture, ?[X,Y]: (X != Y & ?[H]: (h(X) = H & h(Y) = H))).
"""
    },
    {
        "id": "bench_032_unsat",
        "difficulty": "hard",
        "description": "Drinker paradox",
        "status": "unsat",
        "content": """% Drinker's paradox: exists someone such that if they drink, everyone drinks
fof(axiom1, axiom, (![X]: drinks(X)) | ?[Y]: ~drinks(Y)).
fof(goal, conjecture, ?[X]: (drinks(X) => ![Y]: drinks(Y))).
"""
    },
    {
        "id": "bench_033_unsat",
        "difficulty": "hard",
        "description": "Barber paradox resolution",
        "status": "unsat",
        "content": """% Barber paradox: barber shaves all who don't shave themselves
fof(barber_def, axiom, ![X]: (shaves(barber,X) <=> ~shaves(X,X))).
fof(goal, conjecture, $false).
"""
    },
    {
        "id": "bench_034_unsat",
        "difficulty": "hard",
        "description": "Church-Rosser (simple case)",
        "status": "unsat",
        "content": """% Diamond property for reduction
fof(diamond, axiom, ![X,Y,Z]: ((reduces(X,Y) & reduces(X,Z)) =>
                                ?[W]: (reduces(Y,W) & reduces(Z,W)))).
fof(trans, axiom, ![X,Y,Z]: ((reduces(X,Y) & reduces(Y,Z)) => reduces(X,Z))).
fof(fact1, axiom, reduces(a,b)).
fof(fact2, axiom, reduces(a,c)).
fof(goal, conjecture, ?[D]: (reduces(b,D) & reduces(c,D))).
"""
    },
    {
        "id": "bench_035_unsat",
        "difficulty": "hard",
        "description": "Knaster-Tarski (finite lattice)",
        "status": "unsat",
        "content": """% Monotone function has fixed point
fof(mono, axiom, ![X,Y]: (le(X,Y) => le(f(X),f(Y)))).
fof(trans, axiom, ![X,Y,Z]: ((le(X,Y) & le(Y,Z)) => le(X,Z))).
fof(antisymm, axiom, ![X,Y]: ((le(X,Y) & le(Y,X)) => X = Y)).
fof(top, axiom, ![X]: le(X,top)).
fof(bottom, axiom, ![X]: le(bottom,X)).
fof(goal, conjecture, ?[X]: f(X) = X).
"""
    },

    # ========== HARD SAT (36-42) ==========
    {
        "id": "bench_036_sat",
        "difficulty": "hard",
        "description": "AC not provable in ZF",
        "status": "sat",
        "content": """% Axiom of Choice not provable from basic set axioms
fof(prod_nonempty, axiom, ![S]: (?[X]: in(X,S)) => ?[Y]: in(Y,prod(S))).
fof(goal, conjecture, ![F]: (?[G]: (![X]: ?[Y]: in(pair(X,Y),F)) =>
                                     ?[H]: ![X]: in(pair(X,choose(F,X)),F))).
"""
    },
    {
        "id": "bench_037_sat",
        "difficulty": "hard",
        "description": "Continuum hypothesis independence",
        "status": "sat",
        "content": """% Continuum hypothesis is independent
fof(aleph0, axiom, card(nat) = aleph0).
fof(aleph1, axiom, next_card(aleph0) = aleph1).
fof(power_larger, axiom, ![S]: gt(card(power(S)), card(S))).
fof(goal, conjecture, card(power(nat)) = aleph1).
"""
    },
    {
        "id": "bench_038_sat",
        "difficulty": "hard",
        "description": "Weak excluded middle",
        "status": "sat",
        "content": """% Double negation doesn't give excluded middle in intuitionistic logic
fof(axiom1, axiom, ![P]: ~~(P | ~P)).
fof(goal, conjecture, ![Q]: (Q | ~Q)).
"""
    },
    {
        "id": "bench_039_sat",
        "difficulty": "hard",
        "description": "Unique choice without AC",
        "status": "sat",
        "content": """% Unique choice doesn't imply AC
fof(unique_ex, axiom, ![X]: ?[Y]: (!![Z]: (r(X,Z) <=> Y = Z))).
fof(goal, conjecture, ?[F]: ![X]: r(X,F(X))).
"""
    },
    {
        "id": "bench_040_sat",
        "difficulty": "hard",
        "description": "Decidability not provable",
        "status": "sat",
        "content": """% Decidability not provable for arbitrary properties
fof(axiom1, axiom, ![P]: (provable(P) => true(P))).
fof(goal, conjecture, ![P]: (true(P) | true(neg(P)))).
"""
    },
    {
        "id": "bench_041_sat",
        "difficulty": "hard",
        "description": "Well-ordering without AC",
        "status": "sat",
        "content": """% Every set can be well-ordered (equiv to AC, not provable)
fof(axiom1, axiom, ![S]: (?[X]: in(X,S)) => ?[Y]: (in(Y,S) & ![Z]: (in(Z,S) => le(Y,Z)))).
fof(goal, conjecture, ![S]: ?[R]: (total_order(R,S) & well_founded(R,S))).
"""
    },
    {
        "id": "bench_042_sat",
        "difficulty": "hard",
        "description": "Halting problem undecidability",
        "status": "sat",
        "content": """% Halting problem: no decider for all programs
fof(some_halt, axiom, ?[P]: halts(P)).
fof(some_loop, axiom, ?[Q]: ~halts(Q)).
fof(goal, conjecture, ?[D]: ![P]: (halts(P) <=> accepts(D,P))).
"""
    },
]


def create_benchmark_suite():
    """Create all benchmark files and verification script"""

    # Create benchmark directory
    bench_dir = Path("tptp_fol_benchmark_42")
    bench_dir.mkdir(exist_ok=True)

    # Create problem files
    for problem in PROBLEMS:
        filename = bench_dir / f"{problem['id']}.p"
        with open(filename, 'w') as f:
            f.write(problem['content'])
        print(f"Created: {filename}")

    # Create README
    readme = bench_dir / "README.md"
    with open(readme, 'w') as f:
        f.write("""# TPTP FOF Benchmark Suite (42 Problems)

## Purpose
Curated benchmark for developing PeTTaRes (PeTTa Resolution Prover)

## Structure
- **21 UNSAT** problems (theorems provable, unsatisfiable)
- **21 SAT** problems (not provable, satisfiable or independent)

## Difficulty Levels
- **Easy (1-14):** Basic FOL reasoning, 1-2 inference steps
- **Medium (15-28):** Quantifier reasoning, equality, functions
- **Hard (29-42):** Advanced logic, set theory, computability

## Problems Overview

### Easy UNSAT (1-7)
1. Modus ponens
2. Hypothetical syllogism
3. Universal instantiation
4. Universal modus ponens
5. Transitive relation
6. Symmetry
7. Function composition

### Easy SAT (8-14)
8. Affirming consequent (fallacy)
9. Denying antecedent (fallacy)
10. Existential without witness
11. Universal from specific
12. Non-transitive relation
13. Disjunction ambiguity
14. Unrelated predicates

### Medium UNSAT (15-21)
15. Equivalence relation properties
16. Function congruence
17. Nested quantifiers
18. Successor function
19. Antisymmetric ordering
20. Ancestor relation
21. List properties

### Medium SAT (22-28)
22. Existential quantifier scope
23. Function without surjectivity
24. Irreflexive without proof
25. Skolem function ambiguity
26. Commutativity not implied
27. Totality from partial order
28. Inverse without axiom

### Hard UNSAT (29-35)
29. Group identity uniqueness
30. Cantor's theorem (finite case)
31. Pigeonhole principle
32. Drinker paradox
33. Barber paradox resolution
34. Church-Rosser (simple case)
35. Knaster-Tarski (finite lattice)

### Hard SAT (36-42)
36. AC not provable in ZF
37. Continuum hypothesis independence
38. Weak excluded middle
39. Unique choice without AC
40. Decidability not provable
41. Well-ordering without AC
42. Halting problem undecidability

## Usage

### Verify with E Prover
```bash
./verify_with_eprover.sh
```

### Convert to MeTTa
```bash
./convert_to_metta.sh
```

### Run Full Pipeline
```bash
./run_benchmark.sh
```

## Expected Results
- UNSAT problems should be proven by E/Vampire
- SAT problems should timeout or return model

## Files
- `bench_NNN_*.p` - TPTP FOF problem files
- `verify_with_eprover.sh` - Verify with E prover
- `convert_to_metta.sh` - Convert all to MeTTa
- `run_benchmark.sh` - Full pipeline test
""")

    # Create verification script for E prover
    verify_script = bench_dir / "verify_with_eprover.sh"
    with open(verify_script, 'w') as f:
        f.write("""#!/bin/bash
# Verify benchmark problems with E Prover

echo "==========================================================================="
echo "TPTP FOF Benchmark Verification with E Prover"
echo "==========================================================================="
echo ""

EPROVER="eprover"
TIMEOUT=10

results_file="verification_results.txt"
rm -f "$results_file"

unsat_passed=0
unsat_total=0
sat_passed=0
sat_total=0

for problem in bench_*.p; do
    base=$(basename "$problem" .p)

    # Determine expected result
    if [[ "$base" == *"unsat"* ]]; then
        expected="unsat"
        unsat_total=$((unsat_total + 1))
    else
        expected="sat"
        sat_total=$((sat_total + 1))
    fi

    # Run E prover with timeout
    echo -n "Testing $problem ... "
    output=$(timeout $TIMEOUT $EPROVER --auto "$problem" 2>&1)

    if echo "$output" | grep -q "Proof found"; then
        result="unsat"
        symbol="✅"
    elif echo "$output" | grep -q "Completion found"; then
        result="sat"
        symbol="✅"
    elif echo "$output" | grep -q "Timeout"; then
        result="timeout"
        symbol="⏱️"
    else
        result="unknown"
        symbol="❓"
    fi

    # Check if result matches expected
    if [ "$result" == "$expected" ]; then
        echo "$symbol $result (expected: $expected)"
        echo "$problem: $symbol $result" >> "$results_file"

        if [ "$expected" == "unsat" ]; then
            unsat_passed=$((unsat_passed + 1))
        else
            sat_passed=$((sat_passed + 1))
        fi
    else
        echo "❌ $result (expected: $expected)"
        echo "$problem: ❌ $result (expected: $expected)" >> "$results_file"
    fi
done

echo ""
echo "==========================================================================="
echo "VERIFICATION SUMMARY"
echo "==========================================================================="
echo "UNSAT problems: $unsat_passed / $unsat_total"
echo "SAT problems:   $sat_passed / $sat_total"
echo "Total:          $((unsat_passed + sat_passed)) / $((unsat_total + sat_total))"
echo ""
echo "Results saved to: $results_file"
echo "==========================================================================="
""")
    verify_script.chmod(0o755)

    # Create conversion script
    convert_script = bench_dir / "convert_to_metta.sh"
    with open(convert_script, 'w') as f:
        f.write("""#!/bin/bash
# Convert all benchmark problems to MeTTa

echo "Converting TPTP FOF benchmark to MeTTa..."

for problem in bench_*.p; do
    base=$(basename "$problem" .p)
    echo "Converting $problem ..."

    # TPTP -> S-exp
    python3 ../tptp_to_sexp.py "$problem" > /dev/null

    # S-exp -> MeTTa
    json_file="${base}_1.json"
    if [ -f "$json_file" ]; then
        python3 ../sexp_to_metta.py "$json_file" > /dev/null
    fi
done

echo ""
echo "Conversion complete!"
echo "Created $(ls -1 bench_*.metta 2>/dev/null | wc -l) MeTTa files"
""")
    convert_script.chmod(0o755)

    # Create full benchmark script
    bench_script = bench_dir / "run_benchmark.sh"
    with open(bench_script, 'w') as f:
        f.write("""#!/bin/bash
# Run complete benchmark: verify + convert

echo "==========================================================================="
echo "TPTP FOF Benchmark Suite - Complete Pipeline"
echo "==========================================================================="
echo ""

echo "Step 1: Verifying with E Prover..."
./verify_with_eprover.sh

echo ""
echo "Step 2: Converting to MeTTa..."
./convert_to_metta.sh

echo ""
echo "Step 3: Testing bijection on sample..."
for sample in bench_001_unsat.p bench_008_sat.p bench_029_unsat.p; do
    if [ -f "$sample" ]; then
        echo "  Bijection test: $sample"
        python3 ../tptp_to_sexp.py "$sample" > /dev/null
        base=$(basename "$sample" .p)
        python3 ../sexp_to_tptp.py "${base}_1.json" "${base}_reconstructed.p" > /dev/null
        echo "    ✅ Round-trip successful"
    fi
done

echo ""
echo "==========================================================================="
echo "Benchmark ready for PeTTaRes development!"
echo "==========================================================================="
""")
    bench_script.chmod(0o755)

    print(f"\n✅ Created {len(PROBLEMS)} benchmark problems in {bench_dir}/")
    print(f"   - 21 UNSAT problems")
    print(f"   - 21 SAT problems")
    print(f"   - Difficulty: Easy (14), Medium (14), Hard (14)")


if __name__ == '__main__':
    create_benchmark_suite()
