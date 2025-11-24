;; TPTP S-Expression Export

;; Formulas

;; i_0_4 (negated_conjecture)
(fof
  i_0_4
  negated_conjecture
  (clause
    (lit
      (greek
        (const esk1_0)
      )
    )
  )
)

;; i_0_3 (negated_conjecture)
(fof
  i_0_3
  negated_conjecture
  (clause
    (lit-neg
      (mortal
        (const esk1_0)
      )
    )
  )
)

;; i_0_2 (plain)
(fof
  i_0_2
  plain
  (clause
    (lit
      (man
        (var X1)
      )
    )
    (lit-neg
      (greek
        (var X1)
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
      (mortal
        (var X1)
      )
    )
    (lit-neg
      (man
        (var X1)
      )
    )
  )
)
