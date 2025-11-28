;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CNF Clauses for Propositional Resolution
;;; Auto-generated from TPTP via E Prover
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; i_0_1 (plain): knight_a | knave_a
(axiom (lit knight_a) (lit knave_a))

;; i_0_2 (plain): knight_b | knave_b
(axiom (lit knight_b) (lit knave_b))

;; i_0_5 (plain): statement_a | ~knave_b
(axiom (lit statement_a) (nlit knave_b))

;; i_0_6 (plain): statement_a | ~knave_a
(axiom (lit statement_a) (nlit knave_a))

;; i_0_8 (plain): statement_a | ~knight_a
(axiom (lit statement_a) (nlit knight_a))

;; i_0_3 (plain): ~knight_a | ~knave_a
(axiom (nlit knight_a) (nlit knave_a))

;; i_0_4 (plain): ~knight_b | ~knave_b
(axiom (nlit knight_b) (nlit knave_b))

;; i_0_9 (plain): ~knave_a | ~statement_a
(axiom (nlit knave_a) (nlit statement_a))

;; i_0_10 (negated_conjecture): ~knight_a | ~knave_b
(goal (nlit knight_a) (nlit knave_b))

;; i_0_7 (plain): knave_a | knave_b | ~statement_a
(axiom (lit knave_a) (lit knave_b) (nlit statement_a))


;; Ready for resolution!
! "CNF loaded - tagged format for pattern matching"
