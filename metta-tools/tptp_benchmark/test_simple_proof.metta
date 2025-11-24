;;; Simple manual test of PeTTaRes prover
;;; Avoids non-determinism issues by testing individual function calls

!(import! &self superposition)

!(println! "\n=== PeTTaRes Simple Proof Test ===\n")

;; Test 1: Binary resolution on {P(a), ~P(a)}
!(println! "Test 1: Binary resolution - {P(a), ~P(a)}")
(= test-1-c1 (Clause (((⩳ (Fun P ((Fun a ()))) true) true))))
(= test-1-c2 (Clause (((⩳ (Fun P ((Fun a ()))) true) false))))

!(let $result (binary-resolution test-1-c1 test-1-c2)
   (case $result
     (((Clause $lits)
       (if (== $lits ())
           (println! "✅ Binary resolution produced empty clause")
           (println! (:: "❌ Expected empty clause, got:" $lits))))
      ($_ (println! (:: "❌ Binary resolution failed:" $result))))))

;; Test 2: Full prover on {P(a), ~P(a)}
!(println! "\nTest 2: Full prover - {P(a), ~P(a)}")
(= test-2-axioms (cons-atom
                   (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                   (cons-atom
                     (Clause (((⩳ (Fun P ((Fun a ()))) true) false)))
                     ())))

!(println! "Running prover with FIFO strategy...")
!(let $result (prove test-2-axioms (FIFO))
   (if (== $result (UNSAT))
       (println! "✅ Prover detected UNSAT")
       (println! (:: "Result:" $result))))

;; Test 3: Equality resolution on {a ≠ a}
!(println! "\nTest 3: Equality resolution - {a ≠ a}")
(= test-3-clause (Clause (((⩳ (Fun a ()) (Fun a ())) false))))

!(let $result (equality-resolution test-3-clause)
   (case $result
     (((Clause $lits)
       (if (== $lits ())
           (println! "✅ Equality resolution produced empty clause")
           (println! (:: "❌ Expected empty clause, got:" $lits))))
      ($_ (println! (:: "❌ Equality resolution failed:" $result))))))

;; Test 4: Full prover on {a ≠ a}
!(println! "\nTest 4: Full prover - {a ≠ a}")
(= test-4-axioms (cons-atom
                   (Clause (((⩳ (Fun a ()) (Fun a ())) false)))
                   ()))

!(let $result (prove test-4-axioms (FIFO))
   (if (== $result (UNSAT))
       (println! "✅ Prover detected UNSAT")
       (println! (:: "Result:" $result))))

;; Test 5: Saturation on single fact {P(a)}
!(println! "\nTest 5: Saturation - {P(a)}")
(= test-5-axioms (cons-atom
                   (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                   ()))

!(let $result (prove test-5-axioms (FIFO))
   (if (== $result (Saturated))
       (println! "✅ Prover saturated (no contradiction)")
       (println! (:: "Result:" $result))))

!(println! "\n=== Test Complete ===\n")
