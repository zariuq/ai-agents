;;; Test PeTTaRes with TPTP SYN046+1 (Pelletier 15)
;;;
;;; Original TPTP:
;;;   fof(pel15, conjecture, ((p => q) <=> (~p | q))).
;;;
;;; E Prover CNF (negated conjecture):
;;;   cnf(i_0_5, negated_conjecture, (p)).
;;;   cnf(i_0_2, negated_conjecture, (~q)).
;;;   cnf(i_0_3, negated_conjecture, (p|~q)).
;;;   cnf(i_0_4, negated_conjecture, (p|~q)).  ; duplicate
;;;   cnf(i_0_1, negated_conjecture, (q|~p)).

!(import! &self superposition)

!(println! "\n=== Testing PeTTaRes with TPTP SYN046+1 (Pelletier 15) ===\n")

!(println! "Problem: Is (p => q) <=> (~p | q) a theorem?")
!(println! "Expected: UNSAT (proves theorem by contradiction)\n")

;; Translate CNF to MeTTa clause representation:
;; Unit clauses:
;;   p        = (Clause (((⩳ (Fun p ()) true) true)))
;;   ~q       = (Clause (((⩳ (Fun q ()) true) false)))
;; Multi-literal clauses:
;;   p|~q     = (Clause (((⩳ (Fun p ()) true) true) ((⩳ (Fun q ()) true) false)))
;;   q|~p     = (Clause (((⩳ (Fun q ()) true) true) ((⩳ (Fun p ()) true) false)))

(= (test-pelletier15)
   (let $axioms (cons-atom
                  (Clause (((⩳ (Fun p ()) true) true)))
                  (cons-atom
                    (Clause (((⩳ (Fun q ()) true) false)))
                    (cons-atom
                      (Clause (((⩳ (Fun p ()) true) true) ((⩳ (Fun q ()) true) false)))
                      (cons-atom
                        (Clause (((⩳ (Fun q ()) true) true) ((⩳ (Fun p ()) true) false)))
                        ()))))
     ;; Use collapse to collect all non-deterministic results, then take first
     (let $all-results (collapse (prove $axioms (FIFO)))
       (let $first-result (car-atom $all-results)
         (if (== $first-result (UNSAT))
             (println! "✅ SUCCESS: Proved Pelletier 15 theorem (UNSAT)")
             (println! (:: "❌ FAIL: Expected UNSAT, got:" $first-result)))))))

!(test-pelletier15)

!(println! "\n=== Expected: ✅ SUCCESS message above ===\n")
