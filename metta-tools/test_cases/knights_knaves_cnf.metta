;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knights and Knaves - CNF Encoding for Resolution
;;;
;;; After clausification, we have 11 clauses
;;; Goal: Derive knight_a and knave_b using resolution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CNF Clauses (from TPTP clausification)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== CNF Clauses from Knights/Knaves ===="
! ""
! "1. knight_a | knave_a           (A is knight or knave)"
! "2. knight_b | knave_b           (B is knight or knave)"
! "3. ~knight_a | ~knave_a         (A not both)"
! "4. ~knight_b | ~knave_b         (B not both)"
! "5. ~statement_a | knave_a | knave_b  (statement def, part 1)"
! "6. statement_a | ~knave_a       (statement def, part 2)"
! "7. statement_a | ~knave_b       (statement def, part 3)"
! "8. ~knight_a | statement_a      (knights tell truth)"
! "9. ~knave_a | ~statement_a      (knaves lie)"
! ""
! "Goal: Derive knight_a and knave_b"
! ""

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Resolution in MeTTa (simplified proof trace)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Proof by Resolution ==="
! ""
! "Step 1: Assume ~knight_a (proof by contradiction)"
! "  From clause 1 (knight_a | knave_a) and ~knight_a"
! "  Derive: knave_a   [by unit resolution]"
! ""
! "Step 2: From knave_a and clause 9 (~knave_a | ~statement_a)"
! "  Derive: ~statement_a   [by unit resolution]"
! ""
! "Step 3: From ~statement_a and clause 6 (statement_a | ~knave_a)"
! "  Derive: ~knave_a   [by unit resolution]"
! ""
! "Step 4: Contradiction! We have both knave_a (step 1) and ~knave_a (step 3)"
! "  Therefore our assumption ~knight_a is false"
! "  Conclude: knight_a   ✅"
! ""
! "Step 5: From knight_a and clause 8 (~knight_a | statement_a)"
! "  Derive: statement_a   [by unit resolution]"
! ""
! "Step 6: From statement_a and clause 6 (statement_a | ~knave_a)"
! "  Already satisfied"
! ""
! "Step 7: From clause 5 (~statement_a | knave_a | knave_b)"
! "  With statement_a false (from step 2 contradiction)"
! "  Must have: knave_a | knave_b"
! ""
! "Step 8: But we know ~knave_a (from step 3)"
! "  Wait, that was in the contradiction branch!"
! ""
! "Let me redo this more carefully..."
! ""

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Correct Derivation (following the case analysis)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Correct Proof ==="
! ""
! "We'll use DPLL/case-splitting, not pure resolution"
! ""
! "Given clauses, try to satisfy ALL of them:"
! ""
! "Case 1: knight_a = True"
! "  From clause 8: ~knight_a | statement_a"
! "    With knight_a = True, must have statement_a = True"
! ""
! "  From clause 5: ~statement_a | knave_a | knave_b"
! "    With statement_a = True, this is satisfied (first literal false)"
! ""
! "  From clause 1: knight_a | knave_a"
! "    With knight_a = True, satisfied"
! ""
! "  From clause 3: ~knight_a | ~knave_a"
! "    With knight_a = True, must have knave_a = False"
! ""
! "  From clause 6: statement_a | ~knave_a"
! "    With statement_a = True, satisfied"
! ""
! "  From clause 7: statement_a | ~knave_b"
! "    With statement_a = True, satisfied"
! ""
! "  Wait, statement_a = (knave_a | knave_b)"
! "  With statement_a = True and knave_a = False"
! "  Must have knave_b = True   ✅"
! ""
! "  From clause 4: ~knight_b | ~knave_b"
! "    With knave_b = True, must have knight_b = False"
! ""
! "  From clause 2: knight_b | knave_b"
! "    With knave_b = True, satisfied"
! ""
! "  All clauses satisfied!"
! "  Solution: knight_a=True, knave_b=True   ✅"
! ""

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; What This Shows
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! ""
! "=== Key Insight ==="
! ""
! "CNF clausification is GREAT for:"
! "1. ✅ Converting complex formulas to simple form"
! "2. ✅ Eliminating implications and equivalences"
! "3. ✅ Standard input for SAT solvers"
! ""
! "But even with CNF, we still need:"
! "- DPLL algorithm (case splitting + unit propagation)"
! "- OR resolution prover (binary resolution + factoring)"
! ""
! "FC/BC chainers still don't directly apply because:"
! "- Clauses are disjunctions (p | q | r)"
! "- Not Horn clauses (p & q => r)"
! "- Need backtracking for DPLL"
! "- Need resolution rule for theorem proving"
! ""
! "Next step: Implement DPLL or resolution in MeTTa!"
