;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 1 Tests: Term and Clause Representation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(import! &self ../test_common)
!(import! &self superposition)

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

;; Test 1.4: Equality atoms using ⩳
!(test-eq "equality atom a ⩳ b"
  (⩳ (Fun a ()) (Fun b ()))
  (⩳ (Fun a ()) (Fun b ())))

;; Test 1.5: Literals (signed atoms)
!(test-eq "positive literal: P(a) = true"
  ((⩳ (Fun P ((Fun a ()))) true) true)
  ((⩳ (Fun P ((Fun a ()))) true) true))

!(test-eq "negative literal: P(a) ≠ true"
  ((⩳ (Fun P ((Fun a ()))) true) false)
  ((⩳ (Fun P ((Fun a ()))) true) false))

;; Test 1.6: Clauses (disjunctions of literals)
!(test-eq "unit clause: P(a) = true"
  (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
  (Clause (((⩳ (Fun P ((Fun a ()))) true) true))))

!(test-eq "binary clause: P(X) = true | Q(X) = true"
  (Clause (((⩳ (Fun P ((Var X))) true) true)
           ((⩳ (Fun Q ((Var X))) true) true)))
  (Clause (((⩳ (Fun P ((Var X))) true) true)
           ((⩳ (Fun Q ((Var X))) true) true))))

!(println! "")
!(println! "=== Phase 1: Term/Clause Representation Tests ===")
