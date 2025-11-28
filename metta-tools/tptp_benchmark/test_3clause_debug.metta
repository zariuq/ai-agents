;;; Debug version - see what's happening with 3-clause problem

!(import! &self superposition)

!(println! "\n=== DEBUG: Testing 3-clause problem ===\n")

!(println! "Clauses:")
!(println! "  1. p(a)")
!(println! "  2. ~p(a)")
!(println! "  3. q(a)")
!(println! "Expected: Should find UNSAT from clauses 1 & 2 immediately\n")

;; Add debug wrapper around prove
(= (prove-debug $axioms $strategy)
   (let $result (prove $axioms $strategy)
     (do
       (println! (:: "Result type:" $result))
       $result)))

(= (test-3clause-debug)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun p ((Fun a ()))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun p ((Fun a ()))) true) false)))
                    (cons-atom
                      (Clause (((⩳ (Fun q ((Fun a ()))) true) true)))
                      ())))
     (do
       (println! "Starting proof attempt...")
       (let $all-results (collapse (prove-debug $axioms (FIFO)))
         (do
           (println! (:: "Number of results from collapse:" (length $all-results)))
           (println! (:: "First few results:" (take 5 $all-results)))
           (let $first-result (car-atom $all-results)
             (if (== $first-result (UNSAT))
                 (println! "✅ SUCCESS: Found UNSAT")
                 (println! (:: "❌ UNEXPECTED: Got" $first-result)))))))))

;; Helper to show first N elements
(= (take $n $list)
   (if (or (== $n 0) (== $list ()))
       ()
       (cons-atom (car-atom $list) (take (- $n 1) (cdr-atom $list)))))

;; Helper to count list length
(= (length $list)
   (if (== $list ())
       0
       (+ 1 (length (cdr-atom $list)))))

!(test-3clause-debug)
