;; TPTP S-Expression Export

;; Metadata
;; file: dnf_prop.p
;; domain: Propositional Logic
;; problem: Disjunctive Normal Form example
;; english: Prove (p & q) | (p & r) from p & (q | r)
;; axiom: distributivity premise
;; goal: distributivity conclusion

;; Formulas

;; premise (axiom)
(fof
  premise
  axiom
  (and
    (atom p)
    (or
      (atom q)
      (atom r)
    )
  )
)

;; goal (conjecture)
(fof
  goal
  conjecture
  (or
    (and
      (atom p)
      (atom q)
    )
    (and
      (atom p)
      (atom r)
    )
  )
)
