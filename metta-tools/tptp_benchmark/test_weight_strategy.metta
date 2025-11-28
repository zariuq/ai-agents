;;; Test PeTTaRes with WEIGHT strategy instead of FIFO
;;;
;;; Same 3-clause problem but using WEIGHT strategy

!(import! &self superposition)

!(println! "\n=== Testing PeTTaRes with WEIGHT strategy ===\n")

!(println! "Clauses:")
!(println! "  1. p(a)")
!(println! "  2. ~p(a)")
!(println! "  3. q(a)")
!(println! "Expected: UNSAT with better performance\n")

(= (test-weight-3clause)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun p ((Fun a ()))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun p ((Fun a ()))) true) false)))
                    (cons-atom
                      (Clause (((⩳ (Fun q ((Fun a ()))) true) true)))
                      ())))
     (let $all-results (collapse (prove $axioms (WEIGHT)))  ; WEIGHT instead of FIFO
       (let $first-result (car-atom $all-results)
         (if (== $first-result (UNSAT))
             (println! "✅ SUCCESS: WEIGHT strategy detected UNSAT")
             (println! (:: "❌ FAIL: Expected UNSAT, got:" $first-result)))))))

!(test-weight-3clause)

!(println! "\n=== Expected: ✅ SUCCESS (faster than FIFO) ===\n")
