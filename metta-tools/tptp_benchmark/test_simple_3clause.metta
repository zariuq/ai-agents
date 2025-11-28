;;; Test PeTTaRes with simple 3-clause contradiction
;;;
;;; CNF:
;;;   p(a)
;;;   ~p(a)
;;;   q(a)     ; Extra clause (SAT on its own, but problem is still UNSAT)

!(import! &self superposition)

!(println! "\n=== Testing PeTTaRes with 3-clause problem ===\n")

!(println! "Clauses:")
!(println! "  1. p(a)")
!(println! "  2. ~p(a)")
!(println! "  3. q(a)")
!(println! "Expected: UNSAT (contradiction between 1 and 2)\n")

;; Three clauses
(= (test-3clause)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun p ((Fun a ()))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun p ((Fun a ()))) true) false)))
                    (cons-atom
                      (Clause (((⩳ (Fun q ((Fun a ()))) true) true)))
                      ())))
     (let $all-results (collapse (prove $axioms (FIFO)))
       (let $first-result (car-atom $all-results)
         (if (== $first-result (UNSAT))
             (println! "✅ SUCCESS: Detected contradiction UNSAT in 3-clause problem")
             (println! (:: "❌ FAIL: Expected UNSAT, got:" $first-result)))))))

!(test-3clause)

!(println! "\n=== Expected: ✅ SUCCESS message above ===\n")
