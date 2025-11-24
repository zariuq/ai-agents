;; TPTP S-Expression Export

;; Formulas

;; i_0_2 (plain)
(fof
  i_0_2
  plain
  (clause
    (lit
      (human
        (const socrates)
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
        (const socrates)
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
      (human
        (var X1)
      )
    )
  )
)
