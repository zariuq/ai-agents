;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 2 Tests: Unification and Substitution
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(import! &self ../test_common)
!(import! &self superposition)

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

;; Note: This test is complex - may need multi-substitution support
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

!(println! "")
!(println! "=== Phase 2: Unification and Substitution Tests ===")
