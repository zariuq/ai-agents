;; TPTP S-Expression Export

;; Metadata
;; file: knights_knaves.p
;; domain: Puzzles (Logic)
;; problem: Knights and Knaves - Island puzzle
;; version: Propositional encoding
;; english: On an island, knights always tell the truth and knaves always lie.
;; solution: A is a knight, B is a knave.
;; refs: Classic Raymond Smullyan puzzle
;; status: Theorem

;; Formulas

;; a_is_knight_or_knave (axiom)
(fof
  a_is_knight_or_knave
  axiom
  (or
    (atom knight_a)
    (atom knave_a)
  )
)

;; b_is_knight_or_knave (axiom)
(fof
  b_is_knight_or_knave
  axiom
  (or
    (atom knight_b)
    (atom knave_b)
  )
)

;; a_not_both (axiom)
(fof
  a_not_both
  axiom
  (not
    (and
      (atom knight_a)
      (atom knave_a)
    )
  )
)

;; b_not_both (axiom)
(fof
  b_not_both
  axiom
  (not
    (and
      (atom knight_b)
      (atom knave_b)
    )
  )
)

;; statement_true_def (axiom)
(fof
  statement_true_def
  axiom
  (iff
    (atom statement_a)
    (or
      (atom knave_a)
      (atom knave_b)
    )
  )
)

;; a_knight_implies_truth (axiom)
(fof
  a_knight_implies_truth
  axiom
  (implies
    (atom knight_a)
    (atom statement_a)
  )
)

;; a_knave_implies_false (axiom)
(fof
  a_knave_implies_false
  axiom
  (implies
    (atom knave_a)
    (not
      (atom statement_a)
    )
  )
)

;; conclusion (conjecture)
(fof
  conclusion
  conjecture
  (and
    (atom knight_a)
    (atom knave_b)
  )
)
