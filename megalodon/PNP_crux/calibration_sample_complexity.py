#!/usr/bin/env python3
"""
CALIBRATION SAMPLE COMPLEXITY ANALYSIS

The switching argument in Goertzel's P!=NP proof relies on:
  "Optimal predictor for symmetrized surrogate = optimal predictor for truth"

This is the CALIBRATION claim (Lemma A.16).

With polylog(m) symmetrization samples, does calibration actually hold?

This script numerically investigates the sample complexity requirements.
"""

import numpy as np
import random
from typing import List, Tuple, Dict, Callable
from collections import Counter
import math


def generate_planted_3sat(n: int, m: int, seed: int = 42):
    """Generate planted 3-SAT instance."""
    random.seed(seed)
    np.random.seed(seed)

    planted = np.random.randint(0, 2, n)
    clauses = []
    signs = []

    for _ in range(m):
        vars = tuple(sorted(np.random.choice(n, 3, replace=False)))
        while True:
            s = tuple(np.random.randint(0, 2, 3))
            # Check if planted satisfies clause
            satisfied = any(
                (planted[vars[j]] == s[j]) or (planted[vars[j]] != s[j] and s[j] == 0)
                for j in range(3)
            )
            # Actually: literal (v, s) is satisfied if X[v] == s
            satisfied = any(
                planted[vars[j]] == s[j]
                for j in range(3)
            )
            if satisfied:
                break
        clauses.append(vars)
        signs.append(s)

    return planted, clauses, signs


def apply_sign_flip(planted: np.ndarray, i: int) -> np.ndarray:
    """Apply T_i: flip bit i of the planted solution."""
    result = planted.copy()
    result[i] = 1 - result[i]
    return result


def simple_predictor(features: np.ndarray, coeffs: np.ndarray) -> int:
    """Simple linear predictor: sign(coeffs . features)."""
    return int(np.dot(coeffs, features) >= 0)


def extract_features(clauses: List, signs: List, var_i: int, n: int, depth: int = 2) -> np.ndarray:
    """
    Extract local features for variable i.
    Returns feature vector representing local neighborhood structure.
    """
    # Simple feature: count of positive/negative appearances
    pos_count = 0
    neg_count = 0
    neighbor_degrees = []

    for clause, sign in zip(clauses, signs):
        if var_i in clause:
            idx = clause.index(var_i)
            if sign[idx] == 1:
                pos_count += 1
            else:
                neg_count += 1

            # Count neighbor degrees
            for j in range(3):
                if clause[j] != var_i:
                    neighbor_degrees.append(sum(1 for c in clauses if clause[j] in c))

    features = [
        pos_count,
        neg_count,
        pos_count - neg_count,  # polarity bias
        len(neighbor_degrees),
        np.mean(neighbor_degrees) if neighbor_degrees else 0,
        np.std(neighbor_degrees) if len(neighbor_degrees) > 1 else 0,
    ]

    return np.array(features)


def evaluate_predictor(predictor_fn: Callable, instances: List, targets: List) -> float:
    """Evaluate predictor accuracy on instances."""
    correct = 0
    for inst, target in zip(instances, targets):
        pred = predictor_fn(inst)
        if pred == target:
            correct += 1
    return correct / len(instances) if instances else 0


def symmetrize_predictor(predictor_fn: Callable, family_size: int, n: int) -> Callable:
    """
    Create symmetrized predictor that averages over sign flips.

    In the actual proof, this applies T_i transformations.
    Here we simulate by randomly flipping bits.
    """
    def symmetrized(features: np.ndarray) -> int:
        votes = []
        for _ in range(family_size):
            # Apply random sign flip to features (simulating T_I)
            flipped = features.copy()
            # Randomly perturb features (simulating sign flip effect)
            mask = np.random.randint(0, 2, len(features))
            flipped = flipped * (1 - 2 * (mask * 0.1))  # small perturbation
            votes.append(predictor_fn(flipped))
        # Majority vote
        return int(np.mean(votes) >= 0.5)
    return symmetrized


def find_optimal_predictor(hypothesis_class: List[np.ndarray],
                           instances: List[np.ndarray],
                           targets: List[int]) -> Tuple[int, float]:
    """
    Find the optimal predictor from hypothesis class.
    Returns (index of best predictor, its error rate).
    """
    best_idx = 0
    best_error = float('inf')

    for idx, coeffs in enumerate(hypothesis_class):
        predictor = lambda x, c=coeffs: simple_predictor(x, c)
        error = 1 - evaluate_predictor(predictor, instances, targets)
        if error < best_error:
            best_error = error
            best_idx = idx

    return best_idx, best_error


def test_calibration_sample_complexity():
    """
    Test whether polylog samples suffice for calibration.

    The calibration claim: optimal predictor for surrogate Y~ equals
    optimal predictor for truth X.

    We test: With finite samples, how often does ERM find the same optimal?
    """
    print("=" * 70)
    print("CALIBRATION SAMPLE COMPLEXITY TEST")
    print("=" * 70)
    print()

    results = []

    for n in [50, 100, 200]:
        m = int(2.5 * n)  # clause density 2.5

        # Polylog(m) samples - in practice log^2(m)
        polylog_samples = max(4, int((np.log2(m) ** 2)))

        print(f"n={n}, m={m}, polylog(m)={polylog_samples}")

        # Generate instances
        num_instances = 100

        # Create hypothesis class (random linear predictors)
        feature_dim = 6
        num_hypotheses = 50
        hypothesis_class = [np.random.randn(feature_dim) for _ in range(num_hypotheses)]

        calibration_successes = 0
        calibration_trials = 20

        for trial in range(calibration_trials):
            instances_features = []
            true_targets = []

            for inst_idx in range(num_instances):
                planted, clauses, signs = generate_planted_3sat(n, m, seed=trial*1000+inst_idx)
                var_i = random.randint(0, n-1)

                features = extract_features(clauses, signs, var_i, n)
                instances_features.append(features)
                true_targets.append(planted[var_i])

            # Find optimal predictor for TRUE targets X
            opt_idx_true, err_true = find_optimal_predictor(
                hypothesis_class, instances_features, true_targets
            )

            # Generate SURROGATE targets using symmetrization
            surrogate_targets = []
            for i, (features, true_target) in enumerate(zip(instances_features, true_targets)):
                # Simulate symmetrized predictor output
                votes = []
                base_predictor = lambda x, c=hypothesis_class[opt_idx_true]: simple_predictor(x, c)

                for _ in range(polylog_samples):
                    # Apply "sign flip" - perturbation of features
                    perturbed = features + np.random.randn(len(features)) * 0.1
                    votes.append(base_predictor(perturbed))

                surrogate_targets.append(int(np.mean(votes) >= 0.5))

            # Find optimal predictor for SURROGATE targets Y~
            opt_idx_surrogate, err_surrogate = find_optimal_predictor(
                hypothesis_class, instances_features, surrogate_targets
            )

            # Calibration succeeds if same optimal predictor
            if opt_idx_true == opt_idx_surrogate:
                calibration_successes += 1

        success_rate = calibration_successes / calibration_trials
        results.append((n, m, polylog_samples, success_rate))
        print(f"  Calibration success rate: {success_rate:.1%}")
        print()

    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print(f"{'n':>6} {'m':>6} {'samples':>8} {'calibration':>12}")
    print("-" * 40)
    for n, m, samples, rate in results:
        status = "OK" if rate > 0.9 else "PROBLEMATIC" if rate > 0.7 else "FAILS"
        print(f"{n:>6} {m:>6} {samples:>8} {rate:>11.1%} ({status})")

    return results


def test_optimal_predictor_uniqueness():
    """
    Test if optimal predictors are unique.
    If multiple predictors achieve the same error, calibration might fail.
    """
    print()
    print("=" * 70)
    print("OPTIMAL PREDICTOR UNIQUENESS TEST")
    print("=" * 70)
    print()

    n, m = 100, 250
    feature_dim = 6
    num_hypotheses = 100
    num_instances = 200

    hypothesis_class = [np.random.randn(feature_dim) for _ in range(num_hypotheses)]

    instances_features = []
    true_targets = []

    for inst_idx in range(num_instances):
        planted, clauses, signs = generate_planted_3sat(n, m, seed=inst_idx)
        var_i = random.randint(0, n-1)
        features = extract_features(clauses, signs, var_i, n)
        instances_features.append(features)
        true_targets.append(planted[var_i])

    # Compute errors for all hypotheses
    errors = []
    for coeffs in hypothesis_class:
        predictor = lambda x, c=coeffs: simple_predictor(x, c)
        error = 1 - evaluate_predictor(predictor, instances_features, true_targets)
        errors.append(error)

    errors = np.array(errors)
    min_error = np.min(errors)

    # Count near-optimal hypotheses (within 1% of optimal)
    near_optimal = np.sum(errors <= min_error + 0.01)
    at_optimal = np.sum(errors == min_error)

    print(f"Number of hypotheses: {num_hypotheses}")
    print(f"Minimum error: {min_error:.3f}")
    print(f"Hypotheses at minimum: {at_optimal}")
    print(f"Hypotheses within 1% of minimum: {near_optimal}")
    print()

    if at_optimal > 1:
        print("WARNING: Multiple optimal predictors exist!")
        print("This could cause calibration issues if ERM picks different ones")
        print("for truth vs surrogate targets.")
    else:
        print("OK: Unique optimal predictor exists.")

    return at_optimal, near_optimal


def test_concentration_requirements():
    """
    Analyze concentration requirements for calibration.

    For calibration: We need empirical error to concentrate around true error.
    With polylog(m) samples, what's the deviation?
    """
    print()
    print("=" * 70)
    print("CONCENTRATION REQUIREMENTS FOR CALIBRATION")
    print("=" * 70)
    print()

    for log_m in [10, 15, 20]:
        m = 2 ** log_m
        polylog = int(log_m ** 2)

        # Standard deviation of empirical error with k samples
        # For binary outcome: std = sqrt(p(1-p)/k) <= 1/(2*sqrt(k))
        std_dev = 1 / (2 * np.sqrt(polylog))

        # For 95% confidence: error is within 2*std_dev
        confidence_interval = 2 * std_dev

        print(f"m = 2^{log_m}:")
        print(f"  polylog(m) samples: {polylog}")
        print(f"  Std dev of empirical error: {std_dev:.4f}")
        print(f"  95% confidence interval: +/- {confidence_interval:.4f}")

        # For calibration to work reliably, we need:
        # confidence_interval < (gap between best and second-best predictor)
        # Typical gap might be 1-5%, so interval needs to be < 1%

        if confidence_interval < 0.01:
            print(f"  Status: Sufficient for 1% gap")
        elif confidence_interval < 0.05:
            print(f"  Status: Marginal (needs 5% gap)")
        else:
            print(f"  Status: INSUFFICIENT for typical gaps")
        print()


def main():
    print("=" * 70)
    print("CALIBRATION ANALYSIS: THE REAL CRUX OF GOERTZEL'S P!=NP PROOF")
    print("=" * 70)
    print()
    print("The switching argument relies on calibration:")
    print("  optimal_predictor(surrogate Y~) = optimal_predictor(truth X)")
    print()
    print("We investigate whether this holds with polylog(m) samples.")
    print()

    # Test 1: Sample complexity
    results = test_calibration_sample_complexity()

    # Test 2: Uniqueness
    at_opt, near_opt = test_optimal_predictor_uniqueness()

    # Test 3: Concentration
    test_concentration_requirements()

    print("=" * 70)
    print("CONCLUSIONS")
    print("=" * 70)
    print()

    avg_calibration = np.mean([r[3] for r in results])

    if avg_calibration < 0.7:
        print("FINDING: Calibration appears to FAIL with polylog samples!")
        print()
        print("This suggests a potential gap in Goertzel's proof.")
        print("The switching argument may require more samples than claimed.")
    elif avg_calibration < 0.9:
        print("FINDING: Calibration is MARGINAL with polylog samples.")
        print()
        print("Success depends on specific hypothesis class and error gaps.")
        print("The proof may work in some regimes but not others.")
    else:
        print("FINDING: Calibration appears to hold with polylog samples.")
        print()
        print("This supports the validity of the switching argument.")
        print("Need to look for other potential gaps.")

    print()
    print("Next steps:")
    print("  1. Analyze paper's specific symmetrization construction")
    print("  2. Check Lemma A.16 assumptions carefully")
    print("  3. Look for gaps in the calibration proof itself")

    return 0


if __name__ == "__main__":
    exit(main())
