;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simple Binary Resolution - Direct Implementation
;;;
;;; Goal: Given two clauses, return all possible resolvents
;;; Based on: pyprover's Or.resolve_against()
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check if two literals are complementary
(= (complementary (lit $x) (nlit $x)) True)
(= (complementary (nlit $x) (lit $x)) True)
(= (complementary $_ $_) False)

;; Remove one literal from a list
(= (remove-lit $lit ()) ())
(= (remove-lit $lit ($head $tail))
   (if (== $lit $head)
       $tail  ; Skip this one
       (cons $head (remove-lit $lit $tail))))

;; Append two lists
(= (append () $list) $list)
(= (append ($head $tail) $list)
   (cons $head (append $tail $list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Binary Resolution Algorithm
;;;
;;; For each literal L1 in clause1:
;;;   For each literal L2 in clause2:
;;;     If L1 and L2 are complementary:
;;;       Resolvent = (clause1 - L1) ∪ (clause2 - L2)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Main resolution function
;; Returns list of all resolvents (could be multiple if clauses have multiple complementary pairs)
(= (resolve $clause1 $clause2)
   (resolve-iter $clause1 $clause1 $clause2))

;; Iterate through literals in clause1
(= (resolve-iter () $orig-clause1 $clause2) ())
(= (resolve-iter ($lit1 $rest1) $orig-clause1 $clause2)
   (append (resolve-with-lit $lit1 $clause2 $orig-clause1 $clause2)
           (resolve-iter $rest1 $orig-clause1 $clause2)))

;; Try to resolve using $lit1 against all literals in clause2
(= (resolve-with-lit $lit1 () $orig-clause1 $orig-clause2) ())
(= (resolve-with-lit $lit1 ($lit2 $rest2) $orig-clause1 $orig-clause2)
   (if (complementary $lit1 $lit2)
       ;; Found complementary pair! Create resolvent
       (cons (append (remove-lit $lit1 $orig-clause1)
                     (remove-lit $lit2 $orig-clause2))
             (resolve-with-lit $lit1 $rest2 $orig-clause1 $orig-clause2))
       ;; Not complementary, keep trying
       (resolve-with-lit $lit1 $rest2 $orig-clause1 $orig-clause2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! ""
! "=== Simple Resolution Tests ==="
! ""

! "complementary checks:"
! (complementary (lit p) (nlit p))   ; Should be True
! (complementary (nlit p) (lit p))   ; Should be True
! (complementary (lit p) (lit q))    ; Should be False

! ""
! "remove-lit tests:"
! (remove-lit (lit p) ((lit p) (lit q)))         ; Should be ((lit q))
! (remove-lit (lit q) ((lit p) (lit q) (lit r))) ; Should be ((lit p) (lit r))

! ""
! "append tests:"
! (append ((lit p)) ((lit q)))  ; Should be ((lit p) (lit q))

! ""
! "Resolution test 1: (p | q) with (~p | r) => (q | r)"
! (resolve ((lit p) (lit q)) ((nlit p) (lit r)))

! ""
! "Resolution test 2: (p | q) with (~p) => (q)"
! (resolve ((lit p) (lit q)) ((nlit p)))

! ""
! "Resolution test 3: (p) with (~p) => () (contradiction!)"
! (resolve ((lit p)) ((nlit p)))

! ""
! "Resolution test 4: (p | q) with (r | s) => () (no resolution)"
! (resolve ((lit p) (lit q)) ((lit r) (lit s)))
