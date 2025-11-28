;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CNF Clauses for Propositional Resolution
;;; Auto-generated from TPTP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(import! &self prop_resolution.metta)

;; clause1 (axiom)
;;   p | q
;; clause2 (axiom)
;;   ~p | q
;; clause3 (axiom)
;;   p | ~q
;; clause4 (axiom)
;;   ~p | ~q

;; Axiom clauses
(= axioms (
  ((lit p) (lit q))
  ((neg p) (lit q))
  ((lit p) (neg q))
  ((neg p) (neg q))
))

(= all-clauses axioms)

;; Run resolution
! "=== Running Resolution ==="
! (saturate all-clauses 100)
! ""
! "If result is UNSAT, the conjecture is proven!"
