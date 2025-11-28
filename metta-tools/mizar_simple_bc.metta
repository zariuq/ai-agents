;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simplified Mizar Backward Chainer
;;;
;;; Simplest possible version that actually works
;;; for boole-thm-7: x ∈ X → X is non-empty
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knowledge Base - Facts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Facts about elements in sets
(In a mySet)
(In b mySet)
(In c mySet)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rule: XBOOLE_0:def 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If we can find x ∈ X, then X is non-empty
(= (prove (NonEmpty $X))
   (match &self (In $witness $X) (NonEmpty $X)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Direct queries (this is what actually works!)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Simple Backward Chainer ==="

;; Query 1: Is mySet non-empty?
!(prove (NonEmpty mySet))
;; Expected: (NonEmpty mySet) three times (for a, b, c)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; With proof terms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(= (prove-with-witness (NonEmpty $X))
   (match &self (In $witness $X)
     (proof (NonEmpty $X) (by-witness $witness))))

! "=== With Proof Terms ==="

!(prove-with-witness (NonEmpty mySet))
;; Expected: proofs with witnesses a, b, c

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Depth-limited version (prevent infinite recursion)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: Depth Type)
(: Zero Depth)
(: Succ (-> Depth Depth))

;; Base case: check facts
(= (bc (In $x $X) Zero)
   (match &self (In $x $X) (In $x $X)))

;; Recursive case: apply rule
(= (bc (NonEmpty $X) (Succ $d))
   (let $premise (bc (In $witness $X) $d)
     (NonEmpty $X)))

! "=== Depth-Limited BC ==="

;; This will work when let reduction is fixed
;; !(bc (NonEmpty mySet) (Succ Zero))

;; For now, use the simple prove version
!(prove (NonEmpty mySet))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; What this demonstrates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Summary ==="
! "This simplified chainer shows:"
! "1. Pattern matching with 'match &self' works"
! "2. We can prove NonEmpty from In facts"
! "3. Multiple witnesses are found (nondeterminism)"
! "4. Proof terms can be generated"
! ""
! "This is the essence of backward chaining for boole-thm-7!"
! ""
! "The full Nil-style implementation with depth control"
! "requires 'let' reduction to work properly in MeTTa."