;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knights and Knaves - Forward Chaining Encoding
;;;
;;; Classic Raymond Smullyan puzzle encoded for FC/BC chainer
;;; Goal: Prove (and knight_a knave_b)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knowledge Base (Facts we know)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every person is either a knight or a knave (no middle ground)
;; We encode this as: if we can prove "not knight" then "knave" and vice versa

;; For forward chaining, we'd start with what we CAN derive
;; But this problem requires case analysis, so BC is more natural

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rules (Inference rules as horn clauses)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rule 1: If A is a knight, then A's statement is true
;; statement_a <=> (knave_a | knave_b)
;; So if knight_a, then (knave_a | knave_b)
(= (implies-knight-truth)
   (if knight_a
       (or knave_a knave_b)
       False))

;; Rule 2: If A is a knave, then A's statement is false
;; statement_a <=> (knave_a | knave_b)
;; So if knave_a, then NOT (knave_a | knave_b)
;; But knave_a makes (knave_a | knave_b) true, contradiction!
(= (implies-knave-false)
   (if knave_a
       (not (or knave_a knave_b))
       False))

;; Rule 3: A cannot be both knight and knave
(= (not-both-a)
   (not (and knight_a knave_a)))

;; Rule 4: B cannot be both knight and knave
(= (not-both-b)
   (not (and knight_b knave_b)))

;; Rule 5: A must be one or the other
(= (a-is-one)
   (or knight_a knave_a))

;; Rule 6: B must be one or the other
(= (b-is-one)
   (or knight_b knave_b))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Problem: This encoding doesn't fit FC/BC naturally!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Issue with Direct Translation ==="
! "The knights/knaves problem requires:"
! "1. Case analysis (try knight_a, try knave_a)"
! "2. Constraint satisfaction"
! "3. Proof by contradiction"
! ""
! "FC/BC chainers expect:"
! "- Horn clauses: premise1 & premise2 => conclusion"
! "- Not: equivalences, disjunctions, negations as constraints"
! ""
! "This is why TPTP problems often need:"
! "- SAT solver (for propositional)"
! "- SMT solver (for theories)"
! "- Resolution prover"
! ""
! "NOT a simple forward/backward chainer!"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; What we SHOULD do instead
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! ""
! "=== Better Approaches ==="
! ""
! "Option 1: CNF conversion + Resolution"
! "  - Convert to clausal normal form"
! "  - Use resolution prover"
! "  - MeTTa would need resolution rules"
! ""
! "Option 2: SAT encoding"
! "  - Encode as SAT problem"
! "  - Use DPLL algorithm in MeTTa"
! "  - Build truth assignment incrementally"
! ""
! "Option 3: Tableau method"
! "  - Systematic case splitting"
! "  - Track branches and contradictions"
! "  - More natural for this problem"
! ""
! "Option 4: Manual case analysis (what humans do!)"
! "  - Try knight_a: derive consequences"
! "  - Check consistency"
! "  - Try knave_a: derive consequences"
! "  - Find contradiction"
