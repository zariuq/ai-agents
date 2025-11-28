;; TPTP S-Expression Export

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
    (atom q)
  )
)

;; clause3 (axiom)
(fof
  clause3
  axiom
  (or
    (atom p)
    (not
      (atom q)
    )
  )
)

;; clause4 (axiom)
(fof
  clause4
  axiom
  (or
    (not
      (atom p)
    )
    (not
      (atom q)
    )
  )
)
