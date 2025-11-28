;; TPTP S-Expression Export

;; Formulas

;; all_men_mortal (axiom)
(fof
  all_men_mortal
  axiom
  (forall
    (X)
    (implies
      (man
        (var X)
      )
      (mortal
        (var X)
      )
    )
  )
)

;; all_greeks_men (axiom)
(fof
  all_greeks_men
  axiom
  (forall
    (X)
    (implies
      (greek
        (var X)
      )
      (man
        (var X)
      )
    )
  )
)

;; all_greeks_mortal (conjecture)
(fof
  all_greeks_mortal
  conjecture
  (forall
    (X)
    (implies
      (greek
        (var X)
      )
      (mortal
        (var X)
      )
    )
  )
)
