;; CNF from E Prover - Clean format with tags for pattern matching
;; Each clause is tagged with (axiom ...) or (goal ...)
;; Literals: (lit atom) or (nlit atom) for negative literals

;; Axiom clauses
(axiom (lit knight_a) (lit knave_a))
(axiom (lit knight_b) (lit knave_b))
(axiom (lit statement_a) (nlit knave_b))
(axiom (lit statement_a) (nlit knave_a))
(axiom (lit statement_a) (nlit knight_a))
(axiom (nlit knight_a) (nlit knave_a))
(axiom (nlit knight_b) (nlit knave_b))
(axiom (nlit knave_a) (nlit statement_a))
(axiom (lit knave_a) (lit knave_b) (nlit statement_a))

;; Negated goal (for refutation)
(goal (nlit knight_a) (nlit knave_b))

! "CNF loaded - tagged format for pattern matching"


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Binary Resolution
;;;
;;; Given two clauses, find all possible resolvents
;;; Inspired by pyprover's Or.resolve_against()
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check if two literals are complementary
;; (lit p) and (nlit p) are complementary
(= (complementary (lit $x) (nlit $x)) True)
(= (complementary (nlit $x) (lit $x)) True)
(= (complementary $_ $_) False)

;; Remove a literal from a clause (keeping the tag)
;; Example: remove (lit p) from (axiom (lit p) (lit q)) -> (lit q)
(= (remove-from-clause $lit (axiom)) ())
(= (remove-from-clause $lit (axiom $first))
   (if (== $lit $first)
       ()
       ($first)))
(= (remove-from-clause $lit (axiom $first $rest))
   (if (== $lit $first)
       (remove-from-clause $lit (axiom $rest))
       (cons $first (remove-from-clause $lit (axiom $rest)))))

;; Merge two literal lists (for creating resolvent)
(= (merge-lits () $rest) $rest)
(= (merge-lits ($first) $rest) (cons $first $rest))
(= (merge-lits ($first $more) $rest)
   (cons $first (merge-lits $more $rest)))

;; Try to resolve two clauses on complementary literals
;; Returns a resolvent clause or None
(= (try-resolve-on (axiom) (axiom $lits2)) None)
(= (try-resolve-on (axiom $lit1 $rest1) (axiom $lits2))
   (let $result (find-complement $lit1 (axiom $lits2))
     (if (== $result None)
         ;; No complement found, try next literal
         (try-resolve-on (axiom $rest1) (axiom $lits2))
         ;; Found complement! Create resolvent
         (let $remaining1 (remove-from-clause $lit1 (axiom $rest1))
           (let $remaining2 $result
             (axiom (merge-lits $remaining1 $remaining2)))))))

;; Find complement of a literal in a clause, return clause without it
(= (find-complement $lit (axiom)) None)
(= (find-complement $lit (axiom $first $rest))
   (if (complementary $lit $first)
       ;; Found it! Return rest of clause
       $rest
       ;; Keep looking
       (let $rec-result (find-complement $lit (axiom $rest))
         (if (== $rec-result None)
             None
             ;; Prepend $first to the result
             (cons $first $rec-result)))))


! "Resolution functions defined"

;; Test complementary
! (complementary (lit knight_a) (nlit knight_a))
! (complementary (nlit knave_a) (lit knave_a))
! (complementary (lit p) (lit q))

;; Test resolution on simple example
;; (p | q) with (~p | r) should give (q | r)
! "Test: resolve (axiom (lit p) (lit q)) with (axiom (nlit p) (lit r))"
! (try-resolve-on (axiom (lit p) (lit q)) (axiom (nlit p) (lit r)))
