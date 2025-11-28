;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 3: Superposition Inference Tests
;;
;; Following test-driven development ethos from thesis:
;; - Bitesize, verifiable test cases
;; - Systematic coverage of inference rules
;; - Start simple, build complexity incrementally
;; - Compare against E/Vampire behavior where possible
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(import! &self superposition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Equality Resolution
;; Rule: From s≠s | C, derive C (when s unifies with itself)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 1.1: Basic equality resolution - eliminate trivial disequality
;; Input:  X ≠ X | P(a) = true
;; Output: P(a) = true
!(println! "\n=== Test 1.1: Basic equality resolution ===")
!(let $input (Clause (((⩳ (Var X) (Var X)) false) ((⩳ (Fun P ((Fun a ()))) true) true)))
  (let $result (equality-resolution $input)
    (if (== $result (Clause (((⩳ (Fun P ((Fun a ()))) true) true))))
        (println! "✅ Eliminated X ≠ X from clause")
        (println! (:: "❌ Expected" (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                      "Got" $result)))))

;; Test 1.2: Equality resolution with substitution
;; Input:  f(X) ≠ f(a) | Q(X) = true
;; Output: Q(a) = true (after unifying X with a)
!(println! "\n=== Test 1.2: Equality resolution with substitution ===")
!(let $input (Clause (((⩳ (Fun f ((Var X))) (Fun f ((Fun a ())))) false)
                      ((⩳ (Fun Q ((Var X))) true) true)))
  (let $result (equality-resolution $input)
    (if (== $result (Clause (((⩳ (Fun Q ((Fun a ()))) true) true))))
        (println! "✅ Resolved f(X) ≠ f(a) and substituted X → a")
        (println! (:: "❌ Expected" (Clause (((⩳ (Fun Q ((Fun a ()))) true) true)))
                      "Got" $result)))))

;; Test 1.3: No resolution when sides don't unify
;; Input:  a ≠ b | P(x) = true
;; Output: (UnifyFail) or original clause - cannot resolve
!(println! "\n=== Test 1.3: No resolution when sides don't unify ===")
!(let $input (Clause (((⩳ (Fun a ()) (Fun b ())) false)
                      ((⩳ (Fun P ((Var X))) true) true)))
  (let $result (equality-resolution $input)
    (if (== $result (UnifyFail))
        (println! "✅ Cannot resolve a ≠ b (no unification)")
        (println! (:: "❌ Expected UnifyFail, got" $result)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Superposition (Equational Paramodulation)
;; Rule: From s=t and l[u]=r, where u unifies with s, derive l[t]=r
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 2.1: Basic superposition into function term
;; Given: a = b, f(a) = c
;; Derive: f(b) = c
!(println! "\n=== Test 2.1: Basic superposition ===")
!(let $eq1 (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  (let $eq2 (Clause (((⩳ (Fun f ((Fun a ()))) (Fun c ())) true)))
    (let $result (superposition $eq1 $eq2)
      (if (== $result (Clause (((⩳ (Fun f ((Fun b ()))) (Fun c ())) true))))
          (println! "✅ Superposed a=b into f(a)=c to get f(b)=c")
          (println! (:: "❌ Expected" (Clause (((⩳ (Fun f ((Fun b ()))) (Fun c ())) true)))
                        "Got" $result))))))

;; Test 2.2: Superposition with variables
;; Given: f(X) = g(X), f(a) = b
;; Derive: g(a) = b (after substituting X → a)
!(println! "\n=== Test 2.2: Superposition with variables ===")
!(let $eq1 (Clause (((⩳ (Fun f ((Var X))) (Fun g ((Var X)))) true)))
  (let $eq2 (Clause (((⩳ (Fun f ((Fun a ()))) (Fun b ())) true)))
    (let $result (superposition $eq1 $eq2)
      (if (== $result (Clause (((⩳ (Fun g ((Fun a ()))) (Fun b ())) true))))
          (println! "✅ Superposed f(X)=g(X) into f(a)=b to get g(a)=b")
          (println! (:: "❌ Expected" (Clause (((⩳ (Fun g ((Fun a ()))) (Fun b ())) true)))
                        "Got" $result))))))

;; Test 2.3: Superposition into nested position
;; Given: a = b, f(g(a)) = c
;; Derive: f(g(b)) = c
!(println! "\n=== Test 2.3: Superposition into nested term ===")
!(let $eq1 (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  (let $eq2 (Clause (((⩳ (Fun f ((Fun g ((Fun a ()))))) (Fun c ())) true)))
    (let $result (superposition $eq1 $eq2)
      (if (== $result (Clause (((⩳ (Fun f ((Fun g ((Fun b ()))))) (Fun c ())) true))))
          (println! "✅ Superposed a=b into nested position f(g(a))=c")
          (println! (:: "❌ Expected" (Clause (((⩳ (Fun f ((Fun g ((Fun b ()))))) (Fun c ())) true)))
                        "Got" $result))))))

;; Test 2.4: Multiple possible superposition positions
;; Given: a = b, f(a, a) = c
;; Should derive both: f(b, a) = c AND f(a, b) = c
!(println! "\n=== Test 2.4: Multiple superposition positions ===")
!(let $eq1 (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  (let $eq2 (Clause (((⩳ (Fun f ((Fun a ()) (Fun a ()))) (Fun c ())) true)))
    (let $results (superposition-all $eq1 $eq2)
      ;; Should return list of both derivations
      (if (== (list-length $results) 2)
          (println! "✅ Found both superposition positions")
          (println! (:: "❌ Expected 2 results, got" (list-length $results)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Equality Factoring
;; Rule: From s=t | s'=t' where s and s' unify, derive t=t' | s'=t'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 3.1: Basic equality factoring
;; Given: f(X) = a | f(b) = c
;; With X → b, derive: a = c | f(b) = c
!(println! "\n=== Test 3.1: Basic equality factoring ===")
!(let $input (Clause (((⩳ (Fun f ((Var X))) (Fun a ())) true)
                      ((⩳ (Fun f ((Fun b ()))) (Fun c ())) true)))
  (let $result (equality-factoring $input)
    (if (== $result (Clause (((⩳ (Fun a ()) (Fun c ())) true)
                             ((⩳ (Fun f ((Fun b ()))) (Fun c ())) true))))
        (println! "✅ Factored f(X)=a | f(b)=c to a=c | f(b)=c")
        (println! (:: "❌ Expected factored clause, got" $result)))))

;; Test 3.2: No factoring when left sides don't unify
;; Given: f(a) = b | g(c) = d
;; Cannot factor (f and g don't unify)
!(println! "\n=== Test 3.2: No factoring when heads don't match ===")
!(let $input (Clause (((⩳ (Fun f ((Fun a ()))) (Fun b ())) true)
                      ((⩳ (Fun g ((Fun c ()))) (Fun d ())) true)))
  (let $result (equality-factoring $input)
    (if (== $result (UnifyFail))
        (println! "✅ Cannot factor f(a)=b | g(c)=d")
        (println! (:: "❌ Expected UnifyFail, got" $result)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Integration Tests - Complete Derivations
;; These tests verify that sequences of inferences work together
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 4.1: Derive contradiction from inconsistent equalities
;; Given: a = b, b = c, a ≠ c | $false = true
;; Should derive: $false = true (contradiction)
!(println! "\n=== Test 4.1: Derive contradiction via transitive chain ===")
!(let $eq1 (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  (let $eq2 (Clause (((⩳ (Fun b ()) (Fun c ())) true)))
    (let $eq3 (Clause (((⩳ (Fun a ()) (Fun c ())) false) ((⩳ false true) true)))
      ;; Step 1: Superpose a=b into b=c to get a=c
      (let $derived_ac (superposition $eq1 $eq2)
        ;; Step 2: Use a=c to resolve a≠c in eq3
        (let $contradiction (resolve-with-equation $derived_ac $eq3)
          (if (== $contradiction (Clause (((⩳ false true) true))))
              (println! "✅ Derived contradiction: false = true")
              (println! (:: "❌ Expected contradiction, got" $contradiction))))))))

;; Test 4.2: Simple proof of symmetry: a=b ⟹ b=a
;; This tests if we can derive symmetry using equality axioms
!(println! "\n=== Test 4.2: Derive symmetry of equality ===")
!(let $eq (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  ;; Using reflexivity X=X and superposition should give us b=a
  (let $reflexivity (Clause (((⩳ (Var X) (Var X)) true)))
    (let $result (derive-symmetry $eq $reflexivity)
      (if (== $result (Clause (((⩳ (Fun b ()) (Fun a ())) true))))
          (println! "✅ Derived b=a from a=b")
          (println! (:: "❌ Expected b=a, got" $result))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5: Edge Cases and Boundary Conditions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 5.1: Empty clause handling
!(println! "\n=== Test 5.1: Empty clause (contradiction) ===")
!(let $empty (Clause ())
  (if (is-contradiction $empty)
      (println! "✅ Recognized empty clause as contradiction")
      (println! "❌ Failed to recognize empty clause")))

;; Test 5.2: Reflexivity always holds (no inference needed)
;; X = X should not generate new clauses
!(println! "\n=== Test 5.2: Reflexivity tautology ===")
!(let $reflex (Clause (((⩳ (Var X) (Var X)) true)))
  (if (is-tautology $reflex)
      (println! "✅ Recognized X=X as tautology")
      (println! "❌ Failed to recognize reflexivity tautology")))

;; Test 5.3: Occurs check prevents infinite terms
;; Should not derive X = f(X)
!(println! "\n=== Test 5.3: Occurs check in superposition ===")
!(let $bad (Clause (((⩳ (Var X) (Fun f ((Var X)))) true)))
  (let $result (normalize-clause $bad)
    (if (== $result (UnifyFail))
        (println! "✅ Occurs check prevented X = f(X)")
        (println! (:: "❌ Occurs check failed, got" $result)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 6: Performance and Scaling Tests
;; These verify the implementation handles realistic theorem proving scenarios
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 6.1: Superposition with deep nesting
;; Given: a=b, f(f(f(f(a)))) = c
;; Should derive: f(f(f(f(b)))) = c
!(println! "\n=== Test 6.1: Deep nesting superposition ===")
!(let $eq (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  (let $deep (Clause (((⩳ (Fun f ((Fun f ((Fun f ((Fun f ((Fun a ()))))))))) (Fun c ())) true)))
    (let $result (superposition $eq $deep)
      (if (== $result (Clause (((⩳ (Fun f ((Fun f ((Fun f ((Fun f ((Fun b ()))))))))) (Fun c ())) true))))
          (println! "✅ Superposed into deeply nested term")
          (println! (:: "❌ Deep nesting failed, got" $result))))))

;; Test 6.2: Multiple literals in clause
;; Test superposition with clauses containing multiple literals
!(println! "\n=== Test 6.2: Multi-literal clause superposition ===")
!(let $eq (Clause (((⩳ (Fun a ()) (Fun b ())) true)))
  (let $multi (Clause (((⩳ (Fun f ((Fun a ()))) (Fun c ())) true)
                       ((⩳ (Fun P ((Var X))) true) true)))
    (let $result (superposition $eq $multi)
      ;; Should superpose into first literal, keep second
      (if (contains-literal $result ((⩳ (Fun P ((Var X))) true) true))
          (println! "✅ Preserved other literals during superposition")
          (println! "❌ Lost literals during superposition")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(println! "\n=================================================================")
!(println! "Phase 3 Test Suite Complete")
!(println! "=================================================================")
!(println! "")
!(println! "Coverage:")
!(println! "  Section 1: Equality Resolution (3 tests)")
!(println! "  Section 2: Superposition (4 tests)")
!(println! "  Section 3: Equality Factoring (2 tests)")
!(println! "  Section 4: Integration Tests (2 tests)")
!(println! "  Section 5: Edge Cases (3 tests)")
!(println! "  Section 6: Performance Tests (2 tests)")
!(println! "")
!(println! "Total: 16 tests")
!(println! "")
!(println! "Next step: Implement inference rules in superposition.metta")
!(println! "=================================================================")
