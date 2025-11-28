;; TPTP S-Expression Export

;; Formulas

;; i_0_2 (plain)
(fof
  i_0_2
  plain
  (clause
    (lit
      (r
        (const a)
        (const b)
      )
    )
  )
)

;; i_0_3 (plain)
(fof
  i_0_3
  plain
  (clause
    (lit
      (r
        (const b)
        (const c)
      )
    )
  )
)

;; i_0_4 (negated_conjecture)
(fof
  i_0_4
  negated_conjecture
  (clause
    (lit-neg
      (r
        (const a)
        (const c)
      )
    )
  )
)

;; i_0_1 (plain)
(fof
  i_0_1
  plain
  (clause
    (lit
      (r
        (var X1)
        (var X3)
      )
    )
    (lit-neg
      (r
        (var X2)
        (var X3)
      )
    )
    (lit-neg
      (r
        (var X1)
        (var X2)
      )
    )
  )
)
