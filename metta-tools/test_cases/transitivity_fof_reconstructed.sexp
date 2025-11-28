;; TPTP S-Expression Export

;; Formulas

;; transitivity (axiom)
(fof
  transitivity
  axiom
  (forall
    (X Y Z)
    (implies
      (and
        (r
          (var X)
          (var Y)
        )
        (r
          (var Y)
          (var Z)
        )
      )
      (r
        (var X)
        (var Z)
      )
    )
  )
)

;; r_ab (axiom)
(fof
  r_ab
  axiom
  (r
    (const a)
    (const b)
  )
)

;; r_bc (axiom)
(fof
  r_bc
  axiom
  (r
    (const b)
    (const c)
  )
)

;; r_ac (conjecture)
(fof
  r_ac
  conjecture
  (r
    (const a)
    (const c)
  )
)
