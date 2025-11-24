;; TPTP S-Expression Export

;; Formulas

;; all_humans_mortal (axiom)
(fof
  all_humans_mortal
  axiom
  (forall
    (X)
    (implies
      (human
        (var X)
      )
      (mortal
        (var X)
      )
    )
  )
)

;; socrates_human (axiom)
(fof
  socrates_human
  axiom
  (human
    (const socrates)
  )
)

;; socrates_mortal (conjecture)
(fof
  socrates_mortal
  conjecture
  (mortal
    (const socrates)
  )
)
