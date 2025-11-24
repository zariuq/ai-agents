;; TPTP S-Expression Export

;; Formulas

;; f_injective (axiom)
(fof
  f_injective
  axiom
  (forall
    (X Y)
    (implies
      (=
        (f
          (var X)
        )
        (f
          (var Y)
        )
      )
      (=
        (var X)
        (var Y)
      )
    )
  )
)

;; f_a_equals_f_b (axiom)
(fof
  f_a_equals_f_b
  axiom
  (=
    (f
      (const a)
    )
    (f
      (const b)
    )
  )
)

;; a_equals_b (conjecture)
(fof
  a_equals_b
  conjecture
  (=
    (const a)
    (const b)
  )
)
