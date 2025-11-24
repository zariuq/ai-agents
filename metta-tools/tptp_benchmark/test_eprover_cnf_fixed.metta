;;; Test PeTTaRes with E Prover's CNF conversion - FIXED VERSION
;;;
;;; Original TPTP:
;;;   fof(axiom1, axiom, p(a)).
;;;   fof(axiom2, axiom, ~p(a)).
;;;
;;; E Prover CNF:
;;;   cnf(i_0_1, plain, (p(a))).
;;;   cnf(i_0_2, plain, (~p(a))).

!(import! &self superposition)

!(println! "\n=== Testing PeTTaRes with E Prover CNF (FIXED) ===\n")

;; Translate CNF to MeTTa clause representation:
;; p(a) = (Clause (((⩳ (Fun p ((Fun a ()))) true) true)))
;; ~p(a) = (Clause (((⩳ (Fun p ((Fun a ()))) true) false)))

!(println! "CNF Clause 1: p(a)")
!(println! "CNF Clause 2: ~p(a)")
!(println! "")

!(println! "Running PeTTaRes prover with FIFO strategy...")

;; FIXED: Wrap in a function with inline clause definitions + collapse for single result
(= (test-eprover-cnf)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun p ((Fun a ()))) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun p ((Fun a ()))) true) false)))
                    ()))
     ;; Use collapse to collect all non-deterministic results, then take first
     (let $all-results (collapse (prove $axioms (FIFO)))
       (let $first-result (car-atom $all-results)
         (if (== $first-result (UNSAT))
             (println! "✅ SUCCESS: Detected contradiction UNSAT (collapse + car-atom took first of many)")
             (println! (:: "❌ FAIL: Expected UNSAT, got:" $first-result)))))))

!(test-eprover-cnf)

!(println! "\n=== Expected: ✅ SUCCESS message above ===\n")
