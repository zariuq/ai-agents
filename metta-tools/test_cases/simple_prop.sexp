;; TPTP S-Expression Export

;; Metadata
;; problem: Basic resolution test

;; Formulas

;; clause1 (axiom)
(fof
  clause1
  axiom
  (or
    (atom p)
    (atom q)
  )
)

;; clause2 (axiom)
(fof
  clause2
  axiom
  (or
    (not
      (atom p)
    )
    (atom r)
  )
)

;; goal (conjecture)
(fof
  goal
  conjecture
  (or
    (atom q)
    (atom r)
  )
)
