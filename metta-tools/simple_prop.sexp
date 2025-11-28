;; TPTP S-Expression Export

;; Metadata
;; file: simple_prop.p
;; domain: Propositional Logic
;; problem: Modus Ponens - Simplest inference
;; english: Given P and P => Q, prove Q

;; Formulas

;; fact_p (axiom)
(fof
  fact_p
  axiom
  (atom p)
)

;; fact_impl (axiom)
(fof
  fact_impl
  axiom
  (implies
    (atom p)
    (atom q)
  )
)

;; goal (conjecture)
(fof
  goal
  conjecture
  (atom q)
)
