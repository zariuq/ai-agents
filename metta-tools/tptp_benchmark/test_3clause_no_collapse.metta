;;; Test 3-clause problem WITHOUT collapse to see if prove returns at all

!(import! &self superposition)

!(println! "\n=== Testing 3-clause without collapse ===\n")

(= (test-3clause-no-collapse)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun p ((Fun a ()))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun p ((Fun a ()))) true) false)))
                    (cons-atom
                      (Clause (((⩳ (Fun q ((Fun a ()))) true) true)))
                      ())))
     ;; NO COLLAPSE - just call prove directly
     (prove $axioms (FIFO))))

!(println! "Calling prove directly (may return multiple results)...")
!(test-3clause-no-collapse)
!(println! "Done!")
