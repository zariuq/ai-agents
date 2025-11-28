;; Just the CNF clauses from E Prover - no resolution logic
;; This is to verify E's CNF output loads correctly in MeTTa

;; Axiom clauses (from E Prover)
(= axioms (
  ((lit knight_a) (lit knave_a))
  ((lit knight_b) (lit knave_b))
  ((lit statement_a) (neg knave_b))
  ((lit statement_a) (neg knave_a))
  ((lit statement_a) (neg knight_a))
  ((neg knight_a) (neg knave_a))
  ((neg knight_b) (neg knave_b))
  ((neg knave_a) (neg statement_a))
  ((lit knave_a) (lit knave_b) (neg statement_a))
))

;; Negated goal (from E Prover)
(= goals (
  ((neg knight_a) (neg knave_b))
))

! "CNF from E Prover loaded successfully!"
! axioms
! "Goals:"
! goals
