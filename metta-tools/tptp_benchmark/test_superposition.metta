;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PeTTaRes Superposition Prover - Test Suite
;;
;; Test-driven development of a superposition-based theorem prover
;; Following E Prover's approach: predicates encoded as P(x) = $true
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(import! &self ../test_common)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 1: Term and Clause Representation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 1.1: Variable representation
!(test-eq "variable X"
  (Var X)
  (Var X))

!(test-eq "variable Y"
  (Var Y)
  (Var Y))

;; Test 1.2: Constant representation
!(test-eq "constant a"
  (Fun a ())
  (Fun a ()))

!(test-eq "constant b"
  (Fun b ())
  (Fun b ()))

;; Test 1.3: Function application
!(test-eq "function f(a)"
  (Fun f ((Fun a ())))
  (Fun f ((Fun a ()))))

!(test-eq "function f(X, a)"
  (Fun f ((Var X) (Fun a ())))
  (Fun f ((Var X) (Fun a ()))))

;; Test 1.4: Predicate encoding (P(x) = $true style)
!(test-eq "positive predicate P(a) = $true"
  (= (Fun P ((Fun a ()))) $true)
  (= (Fun P ((Fun a ()))) $true))

!(test-eq "negative predicate P(a) = $false"
  (= (Fun P ((Fun a ()))) $false)
  (= (Fun P ((Fun a ()))) $false))

;; Test 1.5: Clauses (disjunctions)
!(test-eq "unit clause P(a) = $true"
  (Clause ((= (Fun P ((Fun a ()))) $true)))
  (Clause ((= (Fun P ((Fun a ()))) $true))))

!(test-eq "binary clause P(X) = $true | Q(X) = $true"
  (Clause ((= (Fun P ((Var X))) $true)
           (= (Fun Q ((Var X))) $true)))
  (Clause ((= (Fun P ((Var X))) $true)
           (= (Fun Q ((Var X))) $true))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 2: Unification and Substitution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 2.1: Variable occurs check
!(test-eq "X occurs in X"
  (occurs-in (Var X) (Var X))
  True)

!(test-eq "X occurs in f(X)"
  (occurs-in (Var X) (Fun f ((Var X))))
  True)

!(test-eq "X does not occur in Y"
  (occurs-in (Var X) (Var Y))
  False)

;; Test 2.2: Substitution application
!(test-eq "substitute X with a in X"
  (apply-subst (Subst X (Fun a ())) (Var X))
  (Fun a ()))

!(test-eq "substitute X with a in f(X)"
  (apply-subst (Subst X (Fun a ())) (Fun f ((Var X))))
  (Fun f ((Fun a ()))))

!(test-eq "substitute X with a in Y (no change)"
  (apply-subst (Subst X (Fun a ())) (Var Y))
  (Var Y))

;; Test 2.3: Most general unifier (MGU)
!(test-eq "unify X with a"
  (mgu (Var X) (Fun a ()))
  (Subst X (Fun a ())))

!(test-eq "unify a with a"
  (mgu (Fun a ()) (Fun a ()))
  (SubstEmpty))

!(test-eq "unify f(X) with f(a)"
  (mgu (Fun f ((Var X))) (Fun f ((Fun a ()))))
  (Subst X (Fun a ())))

!(test-eq "unify f(X, Y) with f(a, b)"
  (mgu (Fun f ((Var X) (Var Y))) (Fun f ((Fun a ()) (Fun b ()))))
  (SubstList ((Subst X (Fun a ())) (Subst Y (Fun b ())))))

;; Test 2.4: Unification failures
!(test-eq "cannot unify a with b"
  (mgu (Fun a ()) (Fun b ()))
  (UnifyFail))

!(test-eq "cannot unify f(X) with g(X) (clash)"
  (mgu (Fun f ((Var X))) (Fun g ((Var X))))
  (UnifyFail))

!(test-eq "cannot unify X with f(X) (occurs check)"
  (mgu (Var X) (Fun f ((Var X))))
  (UnifyFail))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 3: Basic Superposition Inference
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 3.1: Superposition Right (basic resolution-style)
;; From: P(a) = $true   and   P(X) = $false | Q(X) = $true
;; Infer: Q(a) = $true

!(test-eq "superposition right: P(a)=$true with P(X)=$false|Q(X)=$true"
  (superpose-right
    (Clause ((= (Fun P ((Fun a ()))) $true)))
    (Clause ((= (Fun P ((Var X))) $false)
             (= (Fun Q ((Var X))) $true))))
  (Clause ((= (Fun Q ((Fun a ()))) $true))))

;; Test 3.2: Superposition with equality
;; From: f(a) = b   and   P(f(X)) = $true
;; Infer: P(b) = $true (when X = a)

!(test-eq "superposition into predicate"
  (superpose-into
    (Clause ((= (Fun f ((Fun a ()))) (Fun b ()))))
    (Clause ((= (Fun P ((Fun f ((Var X))))) $true))))
  (Clause ((= (Fun P ((Fun b ()))) $true))))

;; Test 3.3: Superposition Left
;; From: a = b   and   f(a) = c
;; Infer: f(b) = c

!(test-eq "superposition left: a=b with f(a)=c"
  (superpose-left
    (Clause ((= (Fun a ()) (Fun b ()))))
    (Clause ((= (Fun f ((Fun a ()))) (Fun c ())))))
  (Clause ((= (Fun f ((Fun b ()))) (Fun c ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 4: Simplification Rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 4.1: Tautology deletion
!(test-eq "tautology: P(X) = $true | P(X) = $false"
  (is-tautology
    (Clause ((= (Fun P ((Var X))) $true)
             (= (Fun P ((Var X))) $false))))
  True)

!(test-eq "not tautology: P(X) = $true | Q(X) = $true"
  (is-tautology
    (Clause ((= (Fun P ((Var X))) $true)
             (= (Fun Q ((Var X))) $true))))
  False)

;; Test 4.2: Subsumption
!(test-eq "P(X) subsumes P(a)"
  (subsumes
    (Clause ((= (Fun P ((Var X))) $true)))
    (Clause ((= (Fun P ((Fun a ()))) $true))))
  True)

!(test-eq "P(a) does not subsume P(X)"
  (subsumes
    (Clause ((= (Fun P ((Fun a ()))) $true)))
    (Clause ((= (Fun P ((Var X))) $true))))
  False)

!(test-eq "P(X) subsumes P(X) | Q(X)"
  (subsumes
    (Clause ((= (Fun P ((Var X))) $true)))
    (Clause ((= (Fun P ((Var X))) $true)
             (= (Fun Q ((Var X))) $true))))
  True)

;; Test 4.3: Equality resolution
;; From: s != t | C, if s and t unify with σ
;; Infer: Cσ

!(test-eq "equality resolution: a != X | P(X) = $true"
  (equality-resolution
    (Clause ((= (Fun a ()) (Var X))
             (= (Fun P ((Var X))) $true))))
  (Clause ((= (Fun P ((Fun a ()))) $true))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 5: Clause Database with Spaces
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 5.1: Database initialization
!(test-eq "create empty database"
  (let $db (make-prover-db)
    (is-empty-db? $db))
  True)

;; Test 5.2: Add clause to database
!(test-eq "add clause P(a) = $true"
  (let* (($db (make-prover-db))
         ($clause (Clause ((= (Fun P ((Fun a ()))) $true)))))
    (add-clause! $db $clause)
    (contains-clause? $db $clause))
  True)

;; Test 5.3: Retrieve unifiable clauses
!(test-eq "retrieve clauses unifiable with P(X)"
  (let* (($db (make-prover-db))
         ($c1 (Clause ((= (Fun P ((Fun a ()))) $true))))
         ($c2 (Clause ((= (Fun P ((Fun b ()))) $true))))
         ($c3 (Clause ((= (Fun Q ((Fun a ()))) $true)))))
    (add-clause! $db $c1)
    (add-clause! $db $c2)
    (add-clause! $db $c3)
    (length (get-unifiable $db (Fun P ((Var X))))))
  2)  ;; Should find c1 and c2, not c3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 6: Simple Proof Examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 6.1: Trivial proof (modus ponens)
;; Given: P = $true,  P = $false | Q = $true
;; Prove: Q = $true

!(test-eq "modus ponens proof"
  (let* (($db (make-prover-db))
         ($axiom1 (Clause ((= (Fun P ()) $true))))
         ($axiom2 (Clause ((= (Fun P ()) $false)
                           (= (Fun Q ()) $true)))))
    (add-clause! $db $axiom1)
    (add-clause! $db $axiom2)
    (prove $db 10))  ;; Run for max 10 iterations
  (ProofFound (Clause ((= (Fun Q ()) $true)))))

;; Test 6.2: Proof with variables
;; Given: P(a) = $true,  P(X) = $false | Q(X) = $true
;; Prove: Q(a) = $true

!(test-eq "modus ponens with variables"
  (let* (($db (make-prover-db))
         ($axiom1 (Clause ((= (Fun P ((Fun a ()))) $true))))
         ($axiom2 (Clause ((= (Fun P ((Var X))) $false)
                           (= (Fun Q ((Var X))) $true)))))
    (add-clause! $db $axiom1)
    (add-clause! $db $axiom2)
    (prove $db 10))
  (ProofFound (Clause ((= (Fun Q ((Fun a ()))) $true)))))

;; Test 6.3: Pelletier Problem 1 (tptp_001_theorem.p)
;; ((P => Q) <=> (~P | Q))
;; In CNF and negated:
;;   P = $false | Q = $false | P = $true    (from P => Q => ~P | Q)
;;   P = $true | Q = $true | P = $false     (from ~P | Q => P => Q)
;;   Q = $true | P = $false                 (simplification)
;; Should derive empty clause (refutation)

!(test-eq "Pelletier 1: (P=>Q) <=> (~P|Q)"
  (let* (($db (make-prover-db))
         ;; Axioms from CNF conversion of negated conjecture
         ($c1 (Clause ((= (Fun P ()) $false)
                       (= (Fun Q ()) $true)
                       (= (Fun P ()) $true))))
         ($c2 (Clause ((= (Fun P ()) $true)
                       (= (Fun Q ()) $true)
                       (= (Fun P ()) $false)))))
    (add-clause! $db $c1)
    (add-clause! $db $c2)
    (prove $db 50))  ;; Should find empty clause
  (ProofFound EmptyClause))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 7: Integration with TPTP Pipeline
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 7.1: Load from TPTP S-expression format
!(test-eq "parse TPTP clause from s-exp"
  (parse-tptp-clause
    '(or (not (p a)) (q a)))
  (Clause ((= (Fun p ((Fun a ()))) $false)
           (= (Fun q ((Fun a ()))) $true))))

;; Test 7.2: Run on actual benchmark problem
!(test-eq "solve tptp_001_theorem.p"
  (solve-tptp-file "tptp_001_theorem.p" 100)
  (ProofFound EmptyClause))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test Execution Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(println "")
!(println "=== PeTTaRes Superposition Prover Test Suite ===")
!(println "Phase 1: Term/Clause Representation - Tests 1.1-1.5")
!(println "Phase 2: Unification - Tests 2.1-2.4")
!(println "Phase 3: Superposition Inference - Tests 3.1-3.3")
!(println "Phase 4: Simplification - Tests 4.1-4.3")
!(println "Phase 5: Clause Database - Tests 5.1-5.3")
!(println "Phase 6: Simple Proofs - Tests 6.1-6.3")
!(println "Phase 7: TPTP Integration - Tests 7.1-7.2")
!(println "")
!(println "Run: ./run.sh test_superposition.metta")
