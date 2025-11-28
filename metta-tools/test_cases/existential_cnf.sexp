;; TPTP S-Expression Export

;; Formulas

;; i_0_1 (plain)
(fof
  i_0_1
  plain
  (clause
    (lit
      (loves
        (const esk1_0)
        (var X1)
      )
    )
  )
)

;; i_0_2 (negated_conjecture)
(fof
  i_0_2
  negated_conjecture
  (clause
    (lit-neg
      (loves
        (var X1)
        (const esk2_0)
      )
    )
  )
)
