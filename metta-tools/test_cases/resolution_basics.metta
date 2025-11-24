;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Binary Resolution - Basic Functions
;;;
;;; Given two clauses, find all possible resolvents
;;; Inspired by pyprover's Or.resolve_against()
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check if two literals are complementary
;; (lit p) and (nlit p) are complementary
(: complementary (-> Literal Literal Bool))
(= (complementary (lit $x) (nlit $x)) True)
(= (complementary (nlit $x) (lit $x)) True)
(= (complementary $_ $_) False)

;; Remove a literal from a list of literals
(: remove-lit (-> Literal LitList LitList))
(= (remove-lit $lit ()) ())
(= (remove-lit $lit ($first $rest))
   (if (== $lit $first)
       (remove-lit $lit $rest)
       (cons $first (remove-lit $lit $rest))))

;; Merge two lists (for creating resolvent)
(: merge-lits (-> LitList LitList LitList))
(= (merge-lits () $rest) $rest)
(= (merge-lits ($first $more) $rest)
   (cons $first (merge-lits $more $rest)))

;; Remove duplicates from a list
(: dedupe (-> LitList LitList))
(= (dedupe ()) ())
(= (dedupe ($first $rest))
   (if (member $first $rest)
       (dedupe $rest)
       (cons $first (dedupe $rest))))

;; Check if element is in list
(: member (-> $t (List $t) Bool))
(= (member $x ()) False)
(= (member $x ($first $rest))
   (if (== $x $first)
       True
       (member $x $rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Binary Resolution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Try to resolve two clauses on all pairs of complementary literals
;; Returns a list of all possible resolvents
(: resolve-clauses (-> LitList LitList (List LitList)))
(= (resolve-clauses $lits1 $lits2)
   (resolve-all-pairs $lits1 $lits2 $lits1 $lits2))

;; Try all pairs of literals from the two clauses
(= (resolve-all-pairs () $lits2 $orig1 $orig2) ())
(= (resolve-all-pairs ($lit1 $rest1) $lits2 $orig1 $orig2)
   (let $resolvents-from-lit1 (try-resolve-with-all $lit1 $lits2 $orig1 $orig2)
     (merge-lits $resolvents-from-lit1
                 (resolve-all-pairs $rest1 $lits2 $orig1 $orig2))))

;; Try to resolve one literal from clause1 with all literals in clause2
(= (try-resolve-with-all $lit1 () $orig1 $orig2) ())
(= (try-resolve-with-all $lit1 ($lit2 $rest2) $orig1 $orig2)
   (if (complementary $lit1 $lit2)
       ;; Found complementary pair! Create resolvent
       (let $remaining1 (remove-lit $lit1 $orig1)
         (let $remaining2 (remove-lit $lit2 $orig2)
           (cons (dedupe (merge-lits $remaining1 $remaining2))
                 (try-resolve-with-all $lit1 $rest2 $orig1 $orig2))))
       ;; Not complementary, keep trying
       (try-resolve-with-all $lit1 $rest2 $orig1 $orig2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Test Cases
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! ""
! "=== Testing Basic Resolution ==="
! ""

! "Test 1: complementary literals"
! (complementary (lit p) (nlit p))
! (complementary (nlit p) (lit p))
! (complementary (lit p) (lit q))

! ""
! "Test 2: Simple resolution"
! "  Clause1: (p | q)     - (lit p) (lit q)"
! "  Clause2: (~p | r)    - (nlit p) (lit r)"
! "  Expected: (q | r)    - ((lit q) (lit r))"
! ""
! (resolve-clauses ((lit p) (lit q)) ((nlit p) (lit r)))

! ""
! "Test 3: Resolution to unit clause"
! "  Clause1: (p | q)     - (lit p) (lit q)"
! "  Clause2: (~p)        - (nlit p)"
! "  Expected: (q)        - ((lit q))"
! ""
! (resolve-clauses ((lit p) (lit q)) ((nlit p)))

! ""
! "Test 4: Resolution to empty clause (contradiction)"
! "  Clause1: (p)         - (lit p)"
! "  Clause2: (~p)        - (nlit p)"
! "  Expected: ()         - (())"
! ""
! (resolve-clauses ((lit p)) ((nlit p)))

! ""
! "Test 5: No resolution possible"
! "  Clause1: (p | q)     - (lit p) (lit q)"
! "  Clause2: (r | s)     - (lit r) (lit s)"
! "  Expected: ()         - ()"
! ""
! (resolve-clauses ((lit p) (lit q)) ((lit r) (lit s)))
