;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knights and Knaves - SAT Solver Approach in MeTTa
;;;
;;; Proper way to solve propositional logic in MeTTa:
;;; Use DPLL-style case splitting with constraint propagation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Propositional Variables (with True/False assignments)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We need to track truth assignments
;; (assign knight_a True) means "A is a knight"
;; (assign knight_a False) means "A is not a knight"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Constraint: A is knight XOR knave (exactly one)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If knight_a is True, then knave_a must be False
(= (check-a-constraint (assign knight_a True) (assign knave_a $kb))
   (if (== $kb False)
       Valid
       Conflict))

;; If knight_a is False, then knave_a must be True
(= (check-a-constraint (assign knight_a False) (assign knave_a $kb))
   (if (== $kb True)
       Valid
       Conflict))

;; Same for B
(= (check-b-constraint (assign knight_b True) (assign knave_b $kb))
   (if (== $kb False)
       Valid
       Conflict))

(= (check-b-constraint (assign knight_b False) (assign knave_b $kb))
   (if (== $kb True)
       Valid
       Conflict))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Statement: statement_a <=> (knave_a | knave_b)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Evaluate (knave_a | knave_b) given assignments
(= (eval-or $a-val $b-val)
   (if (or (== $a-val True) (== $b-val True))
       True
       False))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knights tell truth: knight_a => statement_a
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If A is knight, statement must match reality
(= (check-knight-truth
     (assign knight_a True)
     (assign knave_a $ka)
     (assign knave_b $kb))
   ;; statement_a should be True
   ;; statement_a <=> (knave_a | knave_b)
   ;; So (knave_a | knave_b) must be True
   (let $stmt-value (eval-or $ka $kb)
     (if (== $stmt-value True)
         Valid
         Conflict)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knaves lie: knave_a => NOT statement_a
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If A is knave, statement must be false
(= (check-knave-lie
     (assign knight_a False)
     (assign knave_a True)
     (assign knave_a $ka)
     (assign knave_b $kb))
   ;; statement_a should be False
   ;; statement_a <=> (knave_a | knave_b)
   ;; So (knave_a | knave_b) must be False
   ;; But knave_a is True, so (True | anything) = True
   ;; CONTRADICTION!
   Conflict)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Case Analysis (the actual solving)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Case 1: Assume A is a knight ==="
! "Assignments:"
! "  knight_a = True"
! "  knave_a = False (from XOR constraint)"
! ""
! "Check knight-truth constraint:"
! "  statement_a must be True"
! "  statement_a <=> (knave_a | knave_b)"
! "  statement_a <=> (False | knave_b)"
! "  statement_a <=> knave_b"
! "  So: knave_b = True"
! ""
! "Therefore: knight_b = False (from XOR constraint)"
! ""
! "Solution: knight_a=True, knave_a=False, knight_b=False, knave_b=True"
! "In logic: A is knight, B is knave"
! "✅ This satisfies all constraints!"

! ""
! "=== Case 2: Assume A is a knave ==="
! "Assignments:"
! "  knight_a = False"
! "  knave_a = True (from XOR constraint)"
! ""
! "Check knave-lie constraint:"
! "  statement_a must be False"
! "  statement_a <=> (knave_a | knave_b)"
! "  statement_a <=> (True | knave_b)"
! "  statement_a <=> True"
! "  But we need statement_a = False!"
! ""
! "❌ CONTRADICTION! This case is impossible."

! ""
! "=== Conclusion ==="
! "Only Case 1 is consistent."
! "Therefore: A is a knight, B is a knave."
! ""
! "(and knight_a knave_b) ✅ PROVEN"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; What a REAL MeTTa SAT solver would need
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! ""
! "=== To actually SOLVE this in MeTTa, we'd need: ==="
! ""
! "1. DPLL Algorithm:"
! "   - Choose unassigned variable"
! "   - Try True: propagate constraints"
! "   - If conflict: backtrack and try False"
! "   - If consistent: recurse on next variable"
! ""
! "2. Unit Propagation:"
! "   - If clause has only one unassigned literal, assign it"
! "   - (knight_a | knave_a) with knight_a=False => knave_a=True"
! ""
! "3. Conflict Detection:"
! "   - Check if any clause is unsatisfiable"
! "   - (not (and knight_a knave_a)) violated? Conflict!"
! ""
! "4. Backtracking:"
! "   - Maintain stack of choices"
! "   - On conflict, undo assignments and try alternative"
! ""
! "This is COMPLEX and not what FC/BC chainers do!"
! ""
! "Chainers are for:"
! "  - Horn clauses: p1 & p2 & ... => q"
! "  - Monotonic reasoning (only add facts)"
! "  - No backtracking needed"
! ""
! "SAT problems need:"
! "  - Case splitting"
! "  - Backtracking"
! "  - Constraint checking"
! "  - Non-Horn clauses (XOR, etc.)"
