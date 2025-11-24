;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Minimal Test for Theorem boole-7
;;;
;;; Just the essentials to demonstrate witness instantiation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types
(: Object Type)
(: Set Type)

;; Predicates
(: in (-> Object Set Bool))
(: non-empty (-> Set Bool))

;; Definition: non-empty means exists witness
(= (non-empty $X)
   (exists $witness (in $witness $X)))

;; The theorem (simplified)
(: thm7 (-> Object Set Bool))
(= (thm7 $x $X)
   (if (in $x $X)
       (non-empty $X)
       True))

;; Test data
(: a Object)
(: mySet Set)

;; Fact: a is in mySet
(= (in a mySet) True)

;; Query: Is mySet non-empty?
!(thm7 a mySet)

;; Expected output: True or (non-empty mySet)
