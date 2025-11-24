;; TPTP S-Expression Export

;; Metadata
;; file: iff_prop.p
;; domain: Propositional Logic
;; problem: Equivalence (biconditional)
;; english: Given p <=> q and p, prove q

;; Formulas

;; equivalence (axiom)
(fof
  equivalence
  axiom
  (iff
    (atom p)
    (atom q)
  )
)

;; fact_p (axiom)
(fof
  fact_p
  axiom
  (atom p)
)

;; goal (conjecture)
(fof
  goal
  conjecture
  (atom q)
)
