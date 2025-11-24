;; TPTP S-Expression Export

;; Metadata
;; file: negation_prop.p
;; domain: Propositional Logic
;; problem: Double negation elimination
;; english: Prove p from ~ ~ p

;; Formulas

;; double_neg (axiom)
(fof
  double_neg
  axiom
  (not
    (not
      (atom p)
    )
  )
)

;; goal (conjecture)
(fof
  goal
  conjecture
  (atom p)
)
