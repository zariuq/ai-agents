;; TPTP S-Expression Export

;; Formulas

;; i_0_2 (plain)
(fof
  i_0_2
  plain
  (clause
    (lit
      (f
        (const b)=f(a)
      )
    )
  )
)

;; i_0_3 (negated_conjecture)
(fof
  i_0_3
  negated_conjecture
  (clause
    (lit
      (b!=a)
    )
  )
)

;; i_0_1 (plain)
(fof
  i_0_1
  plain
  (clause
    (lit
      (X1=X2)
    )
    (lit
      (f
        (var X1)!=f(X2)
      )
    )
  )
)
