;;; Test PeTTaRes with E Prover's CNF conversion
;;;
;;; Original TPTP:
;;;   fof(axiom1, axiom, p(a)).
;;;   fof(axiom2, axiom, ~p(a)).
;;;
;;; E Prover CNF:
;;;   cnf(i_0_1, plain, (p(a))).
;;;   cnf(i_0_2, plain, (~p(a))).

!(import! &self superposition)

!(println! "\n=== Testing PeTTaRes with E Prover CNF ===\n")

;; Translate CNF to MeTTa clause representation:
;; p(a) = (Clause (((⩳ (Fun p ((Fun a ()))) true) true)))
;; ~p(a) = (Clause (((⩳ (Fun p ((Fun a ()))) true) false)))

(= cnf-clause-1 (Clause (((⩳ (Fun p ((Fun a ()))) true) true))))
(= cnf-clause-2 (Clause (((⩳ (Fun p ((Fun a ()))) true) false))))

!(println! "CNF Clause 1: p(a)")
!(println! "CNF Clause 2: ~p(a)")
!(println! "")

!(println! "Running PeTTaRes prover with FIFO strategy...")
(= problem-clauses (cons-atom cnf-clause-1 (cons-atom cnf-clause-2 ())))

!(let $result (prove problem-clauses (FIFO))
   (println! (:: "Result:" $result)))

!(println! "\n=== Expected: UNSAT (contradiction detected) ===\n")
