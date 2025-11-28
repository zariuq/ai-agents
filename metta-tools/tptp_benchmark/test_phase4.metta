;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 4: Simplification and Subsumption - Test Suite
;;
;; Following the test-driven development approach from Phases 1-3
;; Tests written BEFORE implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(import! &self /home/zar/claude/mizar-rs/metta-tools/tptp_benchmark/superposition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Subsumption Checking (5 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 1.1: Basic subsumption - single literal subsumes multi-literal
;; P(a) subsumes P(a) ∨ Q(b)
!(println! "\n=== Test 1.1: Basic subsumption ===")
!(let $c1 (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
  (let $c2 (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                    ((⩳ (Fun Q ((Fun b ()))) true) true)))
    (if (subsumes $c1 $c2)
        (println! "✅ P(a) subsumes P(a) | Q(b)")
        (println! "❌ Expected P(a) to subsume P(a) | Q(b)"))))

;; Test 1.2: No subsumption - different atoms
;; P(a) does NOT subsume Q(b)
!(println! "\n=== Test 1.2: No subsumption - different atoms ===")
!(let $c1 (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
  (let $c2 (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
    (if (subsumes $c1 $c2)
        (println! "❌ P(a) should NOT subsume Q(b)")
        (println! "✅ Correctly identified no subsumption"))))

;; Test 1.3: Subsumption with variables
;; P(X) subsumes P(a) (variable generalizes constant)
!(println! "\n=== Test 1.3: Subsumption with variables ===")
!(let $c1 (Clause (((⩳ (Fun P ((Var X))) true) true)))
  (let $c2 (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
    (if (subsumes $c1 $c2)
        (println! "✅ P(X) subsumes P(a)")
        (println! "❌ Expected P(X) to subsume P(a)"))))

;; Test 1.4: No reverse subsumption
;; P(a) does NOT subsume P(X) (constant doesn't generalize variable)
!(println! "\n=== Test 1.4: No reverse subsumption ===")
!(let $c1 (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
  (let $c2 (Clause (((⩳ (Fun P ((Var X))) true) true)))
    (if (subsumes $c1 $c2)
        (println! "❌ P(a) should NOT subsume P(X)")
        (println! "✅ Correctly rejected reverse subsumption"))))

;; Test 1.5: Multi-literal subsumption
;; P(X) | Q(a) subsumes P(b) | Q(a) | R(c)
!(println! "\n=== Test 1.5: Multi-literal subsumption ===")
!(let $c1 (Clause (((⩳ (Fun P ((Var X))) true) true)
                   ((⩳ (Fun Q ((Fun a ()))) true) true)))
  (let $c2 (Clause (((⩳ (Fun P ((Fun b ()))) true) true)
                    ((⩳ (Fun Q ((Fun a ()))) true) true)
                    ((⩳ (Fun R ((Fun c ()))) true) true)))
    (if (subsumes $c1 $c2)
        (println! "✅ P(X) | Q(a) subsumes P(b) | Q(a) | R(c)")
        (println! "❌ Expected multi-literal subsumption"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Tautology Detection (4 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 2.1: Basic tautology - P(X) ∨ ¬P(X)
!(println! "\n=== Test 2.1: Basic tautology ===")
!(let $c (Clause (((⩳ (Fun P ((Var X))) true) true)
                  ((⩳ (Fun P ((Var X))) true) false)))
  (if (is-tautology $c)
      (println! "✅ Detected P(X) | ¬P(X) as tautology")
      (println! "❌ Failed to detect basic tautology")))

;; Test 2.2: Tautology with unification - P(a) ∨ ¬P(X)
;; After substitution X→a, becomes P(a) ∨ ¬P(a)
!(println! "\n=== Test 2.2: Tautology with unification ===")
!(let $c (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                  ((⩳ (Fun P ((Var X))) true) false)))
  (if (is-tautology $c)
      (println! "✅ Detected P(a) | ¬P(X) as tautology")
      (println! "❌ Failed to detect tautology with unification")))

;; Test 2.3: Not a tautology - different predicates
!(println! "\n=== Test 2.3: Not a tautology ===")
!(let $c (Clause (((⩳ (Fun P ((Var X))) true) true)
                  ((⩳ (Fun Q ((Var X))) true) false)))
  (if (is-tautology $c)
      (println! "❌ P(X) | ¬Q(X) is NOT a tautology")
      (println! "✅ Correctly identified non-tautology")))

;; Test 2.4: Reflexivity is a tautology - X = X
!(println! "\n=== Test 2.4: Reflexivity tautology ===")
!(let $c (Clause (((⩳ (Var X) (Var X)) true)))
  (if (is-tautology $c)
      (println! "✅ Detected X = X as tautology")
      (println! "❌ Failed to detect reflexivity")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Forward Subsumption (3 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 3.1: Add simpler clause, remove subsumed ones
;; Adding P(a) should remove P(a) | Q(b) from set
!(println! "\n=== Test 3.1: Forward subsumption ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                                       ((⩳ (Fun Q ((Fun b ()))) true) true)))
                   (cons-atom (Clause (((⩳ (Fun R ((Fun c ()))) true) true)))
                              ()))
  (let $new-clause (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
    (let $result (forward-subsume $new-clause $clause-set)
      ;; Result should only contain R(c) - P(a)|Q(b) was subsumed
      (if (== (list-length $result) 1)
          (println! "✅ Forward subsumption removed P(a) | Q(b)")
          (println! "❌ Failed to remove subsumed clause")))))

;; Test 3.2: No subsumption - keep all clauses
!(println! "\n=== Test 3.2: Forward subsumption - no removal ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                   (cons-atom (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
                              ()))
  (let $new-clause (Clause (((⩳ (Fun R ((Fun c ()))) true) true)))
    (let $result (forward-subsume $new-clause $clause-set)
      (if (== (list-length $result) 2)
          (println! "✅ Kept all clauses - no subsumption")
          (println! "❌ Incorrectly removed clauses")))))

;; Test 3.3: Multiple subsumptions
;; P(X) subsumes both P(a) and P(b)
!(println! "\n=== Test 3.3: Multiple forward subsumptions ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                   (cons-atom (Clause (((⩳ (Fun P ((Fun b ()))) true) true)))
                   (cons-atom (Clause (((⩳ (Fun Q ((Fun c ()))) true) true)))
                              ())))
  (let $new-clause (Clause (((⩳ (Fun P ((Var X))) true) true)))
    (let $result (forward-subsume $new-clause $clause-set)
      ;; Should only keep Q(c)
      (if (== (list-length $result) 1)
          (println! "✅ P(X) subsumed both P(a) and P(b)")
          (println! "❌ Failed to remove all subsumed clauses")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Backward Subsumption (3 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 4.1: Don't add subsumed clause
;; P(a) | Q(b) is subsumed by existing P(a) → reject
!(println! "\n=== Test 4.1: Backward subsumption - reject new ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                              ())
  (let $new-clause (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                            ((⩳ (Fun Q ((Fun b ()))) true) true)))
    (if (backward-subsumed $new-clause $clause-set)
        (println! "✅ Rejected P(a) | Q(b) (subsumed by P(a))")
        (println! "❌ Failed to detect backward subsumption"))))

;; Test 4.2: Add non-subsumed clause
!(println! "\n=== Test 4.2: Backward subsumption - accept new ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                              ())
  (let $new-clause (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
    (if (backward-subsumed $new-clause $clause-set)
        (println! "❌ Q(b) should be accepted (not subsumed)")
        (println! "✅ Correctly accepted non-subsumed clause"))))

;; Test 4.3: Variable subsumption check
;; P(a) is subsumed by existing P(X)
!(println! "\n=== Test 4.3: Backward subsumption with variables ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Var X))) true) true)))
                              ())
  (let $new-clause (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
    (if (backward-subsumed $new-clause $clause-set)
        (println! "✅ Rejected P(a) (subsumed by P(X))")
        (println! "❌ Failed to detect variable subsumption"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5: Clause Normalization (4 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 5.1: Remove duplicate literals
;; P(a) | P(a) → P(a)
!(println! "\n=== Test 5.1: Remove duplicate literals ===")
!(let $c (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                  ((⩳ (Fun P ((Fun a ()))) true) true)))
  (let $normalized (normalize-clause $c)
    (if (== (list-length (get-literals $normalized)) 1)
        (println! "✅ Removed duplicate P(a)")
        (println! "❌ Failed to remove duplicates"))))

;; Test 5.2: Sort literals for comparison
;; Normalization should produce same result regardless of order
!(println! "\n=== Test 5.2: Sort literals ===")
!(let $c1 (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                   ((⩳ (Fun Q ((Fun b ()))) true) true)))
  (let $c2 (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)
                    ((⩳ (Fun P ((Fun a ()))) true) true)))
    (if (== (normalize-clause $c1) (normalize-clause $c2))
        (println! "✅ Normalized clauses are equal")
        (println! "❌ Different normalization for same clause"))))

;; Test 5.3: Simplify after substitution
;; After X→a, P(X) | P(a) becomes P(a)
!(println! "\n=== Test 5.3: Simplify after substitution ===")
!(let $c (Clause (((⩳ (Fun P ((Var X))) true) true)
                  ((⩳ (Fun P ((Fun a ()))) true) true)))
  (let $subst (Subst X (Fun a ()))
    (let $after-subst (apply-subst-to-literals $subst (get-literals $c))
      (let $normalized (normalize-clause (Clause $after-subst))
        (if (== (list-length (get-literals $normalized)) 1)
            (println! "✅ Simplified P(a) | P(a) to P(a)")
            (println! "❌ Failed to simplify after substitution"))))))

;; Test 5.4: Remove contradictory literals
;; P(a) | ¬P(a) is a tautology → delete entire clause
!(println! "\n=== Test 5.4: Detect tautology during normalization ===")
!(let $c (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                  ((⩳ (Fun P ((Fun a ()))) true) false)))
  (let $normalized (normalize-clause $c)
    (if (== $normalized (Tautology))
        (println! "✅ Detected P(a) | ¬P(a) as tautology")
        (println! "❌ Failed to detect tautology"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 6: Integration Tests (3 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 6.1: Complete simplification pipeline
;; Add clause, check subsumption, normalize, detect tautology
!(println! "\n=== Test 6.1: Complete simplification pipeline ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                              ())
  (let $new-clause (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                            ((⩳ (Fun P ((Fun a ()))) true) true)))
    ;; Normalize first (removes duplicate)
    (let $normalized (normalize-clause $new-clause)
      ;; Check backward subsumption
      (if (backward-subsumed $normalized $clause-set)
          (println! "✅ Pipeline: normalized and detected subsumption")
          (println! "❌ Pipeline failed")))))

;; Test 6.2: Inference + simplification
;; Superpose, then normalize result
!(println! "\n=== Test 6.2: Inference + simplification ===")
!(let $eq (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  (let $clause (Clause (((⩳ (Fun f ((Fun a ()))) (Fun c ())) true)))
    (let $result (superposition $eq $clause)
      (let $normalized (normalize-clause $result)
        ;; Should produce normalized f(b) = c
        (if (== (list-length (get-literals $normalized)) 1)
            (println! "✅ Superposition + normalization worked")
            (println! "❌ Failed to normalize inference result"))))))

;; Test 6.3: Subsumption prevents redundant inferences
;; Don't perform superposition if result would be subsumed
!(println! "\n=== Test 6.3: Subsumption-aware inference ===")
!(let $clause-set (cons-atom (Clause (((⩳ (Fun P ((Var X))) true) true)))
                              ())
  (let $new-inference (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
    ;; P(a) is subsumed by existing P(X) → don't add
    (if (backward-subsumed $new-inference $clause-set)
        (println! "✅ Prevented redundant inference")
        (println! "❌ Should have detected subsumption"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(println! "\n=================================================================")
!(println! "Phase 4 Test Suite Complete")
!(println! "  Section 1: Subsumption Checking (5 tests)")
!(println! "  Section 2: Tautology Detection (4 tests)")
!(println! "  Section 3: Forward Subsumption (3 tests)")
!(println! "  Section 4: Backward Subsumption (3 tests)")
!(println! "  Section 5: Clause Normalization (4 tests)")
!(println! "  Section 6: Integration Tests (3 tests)")
!(println! "  Total: 22 tests")
!(println! "=================================================================")
