;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CNF Clauses for Propositional Resolution
;;; Auto-generated from TPTP via E Prover
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Include resolution prover definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Propositional Resolution Prover in MeTTa
;;;
;;; Based on binary resolution for CNF clauses
;;; Inspired by pyprover's resolution logic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Propositional Resolution Prover ==="
! ""

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Data Structures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Literal: (lit p) or (neg p)
;; Clause: (clause (lit p) (neg q) (lit r))  -- disjunction p | ~q | r
;; CNF: (cnf clause1 clause2 ...)           -- conjunction of clauses

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Helper Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check if two literals are complementary
;; (lit p) and (neg p) are complementary
(= (complementary (lit $x) (neg $x)) True)
(= (complementary (neg $x) (lit $x)) True)
(= (complementary $x $y) False)

;; Remove a literal from a clause
(= (remove-lit $lit ()) ())
(= (remove-lit $lit ($first $rest))
   (if (== $lit $first)
       (remove-lit $lit $rest)
       (cons $first (remove-lit $lit $rest))))

;; Merge two lists (for combining clauses)
(= (merge-lists () $list) $list)
(= (merge-lists ($first $rest) $list)
   (cons $first (merge-lists $rest $list)))

;; Check if literal is in clause
(= (member $x ()) False)
(= (member $x ($first $rest))
   (if (== $x $first)
       True
       (member $x $rest)))

;; Remove duplicates from clause
(= (dedupe ()) ())
(= (dedupe ($first $rest))
   (if (member $first $rest)
       (dedupe $rest)
       (cons $first (dedupe $rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Binary Resolution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; resolve-clauses: Try to resolve two clauses
;; Returns resolvent clause or Empty if contradiction found
;; Returns None if no resolution possible

;; Base case: try all pairs of literals
(= (try-resolve () $clause2) None)
(= (try-resolve ($lit1 $rest1) $clause2)
   (let $result (try-resolve-with $lit1 $clause2)
     (if (not (== $result None))
         $result
         (try-resolve $rest1 $clause2))))

;; Try to resolve using one specific literal from clause1
(= (try-resolve-with $lit1 ()) None)
(= (try-resolve-with $lit1 ($lit2 $rest2))
   (if (complementary $lit1 $lit2)
       ;; Found complementary pair! Create resolvent
       (let $remaining1 (remove-lit $lit1 $clause1)
         (let $remaining2 (remove-lit $lit2 $clause2)
           (dedupe (merge-lists $remaining1 $remaining2))))
       ;; Keep looking
       (try-resolve-with $lit1 $rest2)))

;; Main resolution function
(= (resolve-clauses $clause1 $clause2)
   (try-resolve $clause1 $clause2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Resolution Loop (Saturation)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Add a new clause to clause set if novel
(= (add-if-novel $clause ()) (list $clause))
(= (add-if-novel $clause ($first $rest))
   (if (== $clause $first)
       ;; Already have this clause
       (cons $first $rest)
       ;; Keep looking
       (cons $first (add-if-novel $clause $rest))))

;; Check if clause set contains empty clause
(= (contains-empty ()) False)
(= (contains-empty (() $rest)) True)
(= (contains-empty ($first $rest))
   (contains-empty $rest))

;; Resolve one clause against all others
(= (resolve-against $clause ()) ())
(= (resolve-against $clause ($other $rest-clauses))
   (let $resolvent (resolve-clauses $clause $other)
     (if (== $resolvent None)
         (resolve-against $clause $rest-clauses)
         ;; Got a resolvent!
         (cons $resolvent (resolve-against $clause $rest-clauses)))))

;; Saturation: repeatedly apply resolution until:
;; - Empty clause found (UNSAT)
;; - No new clauses generated (SAT or incomplete)
(= (saturate $clauses $max-iter)
   (if (<= $max-iter 0)
       (SAT-or-unknown $clauses)
       (if (contains-empty $clauses)
           UNSAT
           ;; Try all resolutions
           (let $new-clauses (gen-all-resolvents $clauses $clauses)
             (let $merged (merge-new-clauses $clauses $new-clauses)
               (if (== (length $merged) (length $clauses))
                   ;; No new clauses - saturated
                   (SAT-or-unknown $clauses)
                   ;; Continue with new clauses
                   (saturate $merged (- $max-iter 1))))))))

;; Generate all resolvents from clause list
(= (gen-all-resolvents () $all-clauses) ())
(= (gen-all-resolvents ($clause $rest) $all-clauses)
   (let $resolvents (resolve-against $clause $all-clauses)
     (merge-lists $resolvents (gen-all-resolvents $rest $all-clauses))))

;; Merge new clauses into existing set
(= (merge-new-clauses $old ()) $old)
(= (merge-new-clauses $old ($new $rest))
   (merge-new-clauses (add-if-novel $new $old) $rest))

(= (SAT-or-unknown $clauses)
   (if (contains-empty $clauses)
       UNSAT
       SAT-or-unknown))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example Usage
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! ""
! "=== Example 1: Simple Contradiction ==="
! ""
! "Clauses:"
! "  1. p | q        (clause (lit p) (lit q))"
! "  2. ~p | q       (clause (neg p) (lit q))"
! "  3. p | ~q       (clause (lit p) (neg q))"
! "  4. ~p | ~q      (clause (neg p) (neg q))"
! ""
! "Expected: UNSAT (all 4 cases lead to contradiction)"
! ""

;; Test resolution on simple example
;; This should derive empty clause

! "Testing complementary:"
! (complementary (lit p) (neg p))
! (complementary (neg p) (lit p))
! (complementary (lit p) (lit q))

! ""
! "Testing resolution:"
;; Resolve (p | q) with (~p | q) should give (q)
! (resolve-clauses ((lit p) (lit q)) ((neg p) (lit q)))

;; Resolve (p | q) with (p | ~q) should give (p)
! (resolve-clauses ((lit p) (lit q)) ((lit p) (neg q)))

;; Resolve (q) with (~q) should give ()  -- contradiction!
! (resolve-clauses ((lit q)) ((neg q)))

! ""
! "=== Example 2: Knights and Knaves (subset) ==="
! ""
! "Let's prove knight_a from simplified axioms:"
! "  1. knight_a | knave_a"
! "  2. ~knight_a | ~knave_a"
! "  3. ~knight_a | statement_a"
! "  4. ~knave_a | ~statement_a"
! ""

;; This is a minimal example - full knights/knaves would have more clauses
;; For now, just demonstrate the resolution mechanism works

! ""
! "=== Resolution Prover Ready! ==="
! ""
! "To use:"
! "  1. Convert problem to CNF clauses"
! "  2. Represent as (clause (lit x) (neg y) ...)"
! "  3. Call (saturate clause-list max-iterations)"
! ""


;; i_0_1 (plain)
;;   knight_a | knave_a
;; i_0_2 (plain)
;;   knight_b | knave_b
;; i_0_5 (plain)
;;   statement_a | ~knave_b
;; i_0_6 (plain)
;;   statement_a | ~knave_a
;; i_0_8 (plain)
;;   statement_a | ~knight_a
;; i_0_3 (plain)
;;   ~knight_a | ~knave_a
;; i_0_4 (plain)
;;   ~knight_b | ~knave_b
;; i_0_9 (plain)
;;   ~knave_a | ~statement_a
;; i_0_10 (negated_conjecture)
;;   ~knight_a | ~knave_b
;; i_0_7 (plain)
;;   knave_a | knave_b | ~statement_a

;; Axiom clauses
(= axioms (
  ((lit knight_a) (lit knave_a))
  ((lit knight_b) (lit knave_b))
  ((lit statement_a) (neg knave_b))
  ((lit statement_a) (neg knave_a))
  ((lit statement_a) (neg knight_a))
  ((neg knight_a) (neg knave_a))
  ((neg knight_b) (neg knave_b))
  ((neg knave_a) (neg statement_a))
  ((lit knave_a) (lit knave_b) (neg statement_a))
))

;; Negated goal clauses (for refutation)
(= goals (
  ((neg knight_a) (neg knave_b))
))

;; All clauses (axioms + negated goals)
(= all-clauses (merge-lists axioms goals))

;; Run resolution
! "=== Running Resolution ==="
! (saturate all-clauses 100)
! ""
! "If result is UNSAT, the conjecture is proven!"
! ""
! "=== CNF Conversion by E Prover (Trusted!) ==="
