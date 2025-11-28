;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; TPTP to MeTTa - Modus Ponens Example
;;;
;;; TPTP Input:
;;;   fof(fact_p, axiom, p).
;;;   fof(fact_impl, axiom, p => q).
;;;   fof(goal, conjecture, q).
;;;
;;; Demonstrates: Simple propositional TPTP is TRIVIAL to convert!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knowledge Base - Facts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; fact_p: p is true
(p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rule: Modus Ponens (from p => q)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If we can prove p, then we can prove q
(= (prove q)
   (match &self (p) q))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Query (Prove the conjecture)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== TPTP Propositional Logic Example ==="
! "Given: p"
! "Given: p => q"
! "Goal: prove q"
! ""

!(prove q)
;; Expected: q

! ""
! "=== Success! ==="
! "This demonstrates how EASY it is to convert TPTP propositional"
! "logic to MeTTa compared to complex Mizar structures!"
