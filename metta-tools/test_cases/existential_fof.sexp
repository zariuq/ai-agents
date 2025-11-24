;; TPTP S-Expression Export

;; Formulas

;; someone_loves_all (axiom)
(fof
  someone_loves_all
  axiom
  (exists
    (X)
    (forall
      (Y)
      (loves
        (var X)
        (var Y)
      )
    )
  )
)

;; all_loved (conjecture)
(fof
  all_loved
  conjecture
  (forall
    (Y)
    (exists
      (X)
      (loves
        (var X)
        (var Y)
      )
    )
  )
)
