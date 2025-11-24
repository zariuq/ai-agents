;;; =============================================================================
;;; Phase 6: Main Proving Loop - Test Suite
;;; =============================================================================
;;;
;;; Tests for the given clause algorithm (saturation-based proving).
;;; Following TDD approach: write tests first, then implement.
;;;
;;; Components under test:
;;; - Main saturation loop (given clause algorithm)
;;; - Proof search with FIFO and WEIGHT strategies
;;; - Empty clause detection (UNSAT)
;;; - Saturation detection (no new clauses)
;;; - Integration of all phases (inference + simplification + selection)

!(import! &self superposition)

!(println! "\n===========================================================")
!(println! "Phase 6: Main Proving Loop - Test Suite")
!(println! "===========================================================\n")

;;; =============================================================================
;;; Section 1: Empty Clause Detection (UNSAT Proofs)
;;; =============================================================================

!(println! "\n=== Section 1: Empty Clause Detection ===\n")

;;; Test 1.1: Immediate contradiction - {P(a), ~P(a)}
;;; Should detect empty clause immediately
!(println! "Test 1.1: Immediate contradiction")
(= (test-1-1)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun P ((Fun a ()))) true) false)))
                    ()))
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ Detected contradiction: P(a) ∧ ¬P(a)")
           (println! (:: "❌ Expected UNSAT, got:" $result))))))

!(test-1-1)

;;; Test 1.2: One-step inference - {P(X), ~P(a)}
;;; Should unify X=a and derive empty clause
!(println! "\nTest 1.2: One-step inference contradiction")
(= (test-1-2)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Var X))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun P ((Fun a ()))) true) false)))
                    ()))
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ Derived contradiction: P(X) ∧ ¬P(a) ⊢ ⊥")
           (println! (:: "❌ Expected UNSAT, got:" $result))))))

!(test-1-2)

;;; Test 1.3: Equality resolution - {a ≠ a}
;;; Should apply equality resolution to get empty clause
!(println! "\nTest 1.3: Equality resolution")
(= (test-1-3)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun a ()) (Fun a ())) false)))
                  ())
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ Equality resolution: a ≠ a ⊢ ⊥")
           (println! (:: "❌ Expected UNSAT, got:" $result))))))

!(test-1-3)

;;; =============================================================================
;;; Section 2: Saturation Detection (No Contradiction)
;;; =============================================================================

!(println! "\n=== Section 2: Saturation Detection ===\n")

;;; Test 2.1: Empty axiom set
;;; Should saturate immediately (no clauses to process)
!(println! "Test 2.1: Empty axiom set")
(= (test-2-1)
   (let $axioms ()
     (let $result (prove $axioms (FIFO))
       (if (== $result (Saturated))
           (println! "✅ Empty set saturates immediately")
           (println! (:: "❌ Expected Saturated, got:" $result))))))

!(test-2-1)

;;; Test 2.2: Single fact - {P(a)}
;;; Should saturate (no inferences possible)
!(println! "\nTest 2.2: Single fact")
(= (test-2-2)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                  ())
     (let $result (prove $axioms (FIFO))
       (if (== $result (Saturated))
           (println! "✅ Single fact saturates: P(a)")
           (println! (:: "❌ Expected Saturated, got:" $result))))))

!(test-2-2)

;;; Test 2.3: Non-overlapping facts - {P(a), Q(b)}
;;; Should saturate (facts don't interact)
!(println! "\nTest 2.3: Non-overlapping facts")
(= (test-2-3)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
                    ()))
     (let $result (prove $axioms (FIFO))
       (if (== $result (Saturated))
           (println! "✅ Non-overlapping facts saturate: P(a), Q(b)")
           (println! (:: "❌ Expected Saturated, got:" $result))))))

!(test-2-3)

;;; =============================================================================
;;; Section 3: Multi-Step Inference
;;; =============================================================================

!(println! "\n=== Section 3: Multi-Step Inference ===\n")

;;; Test 3.1: Transitivity - {a=b, b=c, a≠c}
;;; Should derive a=c by transitivity, then empty clause
!(println! "Test 3.1: Transitivity of equality")
(= (test-3-1)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun b ()) (Fun c ())) true)))
                    (cons-atom
                      (Clause (((⩳ (Fun a ()) (Fun c ())) false)))
                      ())))
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ Transitivity proof: a=b, b=c, a≠c ⊢ ⊥")
           (println! (:: "❌ Expected UNSAT, got:" $result))))))

!(test-3-1)

;;; Test 3.2: Superposition chain - {f(a)=b, g(f(X))=c, g(b)≠c}
;;; Should substitute f(a)→b in g(f(a)) to get g(b)=c
!(println! "\nTest 3.2: Superposition chain")
(= (test-3-2)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun f ((Fun a ()))) (Fun b ())) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun g ((Fun f ((Var X))))) (Fun c ())) true)))
                    (cons-atom
                      (Clause (((⩳ (Fun g ((Fun b ()))) (Fun c ())) false)))
                      ())))
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ Superposition: f(a)=b, g(f(X))=c, g(b)≠c ⊢ ⊥")
           (println! (:: "❌ Expected UNSAT, got:" $result))))))

!(test-3-2)

;;; =============================================================================
;;; Section 4: Strategy Comparison (FIFO vs WEIGHT)
;;; =============================================================================

!(println! "\n=== Section 4: Strategy Comparison ===\n")

;;; Test 4.1: FIFO strategy - same as test 1.2
!(println! "Test 4.1: FIFO strategy")
(= (test-4-1)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Var X))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun P ((Fun a ()))) true) false)))
                    ()))
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ FIFO finds proof")
           (println! (:: "❌ FIFO failed, got:" $result))))))

!(test-4-1)

;;; Test 4.2: WEIGHT strategy - same problem
!(println! "\nTest 4.2: WEIGHT strategy")
(= (test-4-2)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Var X))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun P ((Fun a ()))) true) false)))
                    ()))
     (let $result (prove $axioms (WEIGHT))
       (if (== $result (UNSAT))
           (println! "✅ WEIGHT finds proof")
           (println! (:: "❌ WEIGHT failed, got:" $result))))))

!(test-4-2)

;;; Test 4.3: Both strategies on transitivity
!(println! "\nTest 4.3: Both strategies on transitivity")
(= (test-4-3)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun b ()) (Fun c ())) true)))
                    (cons-atom
                      (Clause (((⩳ (Fun a ()) (Fun c ())) false)))
                      ())))
     (let $fifo-result (prove $axioms (FIFO))
       (let $weight-result (prove $axioms (WEIGHT))
         (if (and (== $fifo-result (UNSAT))
                  (== $weight-result (UNSAT)))
             (println! "✅ Both strategies find proof")
             (println! (:: "❌ FIFO:" $fifo-result ", WEIGHT:" $weight-result)))))))

!(test-4-3)

;;; =============================================================================
;;; Section 5: Simplification Integration
;;; =============================================================================

!(println! "\n=== Section 5: Simplification Integration ===\n")

;;; Test 5.1: Forward subsumption - {P(X), P(a), ~P(a)}
;;; Should remove P(a) as subsumed by P(X), then find UNSAT
!(println! "Test 5.1: Forward subsumption during search")
(= (test-5-1)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Var X))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                    (cons-atom
                      (Clause (((⩳ (Fun P ((Fun a ()))) true) false)))
                      ())))
     (let $result (prove $axioms (FIFO))
       (if (== $result (UNSAT))
           (println! "✅ Forward subsumption working: P(X), P(a), ¬P(a) ⊢ ⊥")
           (println! (:: "❌ Expected UNSAT, got:" $result))))))

!(test-5-1)

;;; Test 5.2: Tautology elimination - {P(X) | ~P(X), ~Q(a)}
;;; Should eliminate tautology, leaving only ~Q(a), which saturates
!(println! "\nTest 5.2: Tautology elimination")
(= (test-5-2)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun P ((Var X))) true) true)
                           ((⩳ (Fun P ((Var X))) true) false)))
                  (cons-atom
                    (Clause (((⩳ (Fun Q ((Fun a ()))) true) false)))
                    ()))
     (let $result (prove $axioms (FIFO))
       (if (== $result (Saturated))
           (println! "✅ Tautology eliminated: P(X)|¬P(X) ignored")
           (println! (:: "❌ Expected Saturated, got:" $result))))))

!(test-5-2)

;;; =============================================================================
;;; Test Summary
;;; =============================================================================

!(println! "\n===========================================================")
!(println! "Phase 6 Test Suite Complete")
!(println! "Expected: 12 tests total")
!(println! "  Section 1 (Empty Clause): 3 tests")
!(println! "  Section 2 (Saturation): 3 tests")
!(println! "  Section 3 (Multi-Step): 2 tests")
!(println! "  Section 4 (Strategies): 3 tests")
!(println! "  Section 5 (Simplification): 2 tests")
!(println! "===========================================================\n")
