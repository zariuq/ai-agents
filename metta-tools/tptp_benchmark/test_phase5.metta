;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 5: Clause Selection Strategies - Test Suite
;;
;; Following TDD approach: tests written BEFORE implementation
;;
;; Goal: Implement FIFO and WEIGHT selection strategies for the given clause loop
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(import! &self /home/zar/claude/mizar-rs/metta-tools/tptp_benchmark/superposition)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Clause Weight Calculation (4 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 1.1: Single literal weight
;; P(a) has weight 2 (predicate P + constant a)
!(println! "\n=== Test 1.1: Single literal weight ===")
!(let $c (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
  (let $w (clause-weight $c)
    (if (== $w 2)
        (println! "✅ P(a) has weight 2")
        (println! (:: "❌ Expected weight 2, got:" $w)))))

;; Test 1.2: Multi-literal weight
;; P(a) | Q(b) has weight 4 (P + a + Q + b)
!(println! "\n=== Test 1.2: Multi-literal weight ===")
!(let $c (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                  ((⩳ (Fun Q ((Fun b ()))) true) true)))
  (let $w (clause-weight $c)
    (if (== $w 4)
        (println! "✅ P(a) | Q(b) has weight 4")
        (println! (:: "❌ Expected weight 4, got:" $w)))))

;; Test 1.3: Nested term weight
;; f(g(a)) = b has weight 4 (f + g + a + b)
!(println! "\n=== Test 1.3: Nested term weight ===")
!(let $c (Clause (((⩳ (Fun f ((Fun g ((Fun a ()))))) (Fun b ())) true)))
  (let $w (clause-weight $c)
    (if (== $w 4)
        (println! "✅ f(g(a)) = b has weight 4")
        (println! (:: "❌ Expected weight 4, got:" $w)))))

;; Test 1.4: Variable weight
;; P(X) | Q(Y) has weight 4 (variables count as 1)
!(println! "\n=== Test 1.4: Variable weight ===")
!(let $c (Clause (((⩳ (Fun P ((Var X))) true) true)
                  ((⩳ (Fun Q ((Var Y))) true) true)))
  (let $w (clause-weight $c)
    (if (== $w 4)
        (println! "✅ P(X) | Q(Y) has weight 4")
        (println! (:: "❌ Expected weight 4, got:" $w)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: FIFO Selection (3 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 2.1: Select first clause from queue
!(println! "\n=== Test 2.1: FIFO - select first ===")
!(let $queue (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
              (cons-atom (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
              (cons-atom (Clause (((⩳ (Fun R ((Fun c ()))) true) true)))
                         ())))
  (let $selected (select-clause-fifo $queue)
    (case $selected
      (((Selected $clause $remaining)
        (if (== $clause (Clause (((⩳ (Fun P ((Fun a ()))) true) true))))
            (if (== (list-length $remaining) 2)
                (println! "✅ FIFO selected P(a), 2 remaining")
                (println! "❌ Wrong remaining count"))
            (println! "❌ Expected P(a) to be selected")))
       ($_ (println! "❌ FIFO selection failed"))))))

;; Test 2.2: FIFO on empty queue
!(println! "\n=== Test 2.2: FIFO - empty queue ===")
!(let $queue ()
  (let $selected (select-clause-fifo $queue)
    (if (== $selected (NoClause))
        (println! "✅ FIFO returns NoClause for empty queue")
        (println! "❌ Expected NoClause"))))

;; Test 2.3: FIFO maintains order
!(println! "\n=== Test 2.3: FIFO - maintains order ===")
!(let $queue (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
              (cons-atom (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
                         ()))
  (let $selected1 (select-clause-fifo $queue)
    (case $selected1
      (((Selected $c1 $remaining1)
        (let $selected2 (select-clause-fifo $remaining1)
          (case $selected2
            (((Selected $c2 $remaining2)
              (if (== $c1 (Clause (((⩳ (Fun P ((Fun a ()))) true) true))))
                  (if (== $c2 (Clause (((⩳ (Fun Q ((Fun b ()))) true) true))))
                      (println! "✅ FIFO: P(a) then Q(b)")
                      (println! "❌ Expected Q(b) second"))
                  (println! "❌ Expected P(a) first")))
             ($_ (println! "❌ Second FIFO selection failed"))))))
       ($_ (println! "❌ First FIFO selection failed"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Weight-Based Selection (4 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 3.1: Select lightest clause
;; P(a) (weight 2) vs P(a)|Q(b) (weight 4) → select P(a)
!(println! "\n=== Test 3.1: WEIGHT - select lightest ===")
!(let $queue (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)
                                 ((⩳ (Fun Q ((Fun b ()))) true) true)))
              (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
              (cons-atom (Clause (((⩳ (Fun R ((Fun c ()))) true) true)))
                         ())))
  (let $selected (select-clause-weight $queue)
    (case $selected
      (((Selected $clause $remaining)
        (if (== $clause (Clause (((⩳ (Fun P ((Fun a ()))) true) true))))
            (println! "✅ WEIGHT selected P(a) (lightest)")
            (println! "❌ Expected P(a) to be selected")))
       ($_ (println! "❌ WEIGHT selection failed"))))))

;; Test 3.2: Weight selection on empty queue
!(println! "\n=== Test 3.2: WEIGHT - empty queue ===")
!(let $queue ()
  (let $selected (select-clause-weight $queue)
    (if (== $selected (NoClause))
        (println! "✅ WEIGHT returns NoClause for empty queue")
        (println! "❌ Expected NoClause"))))

;; Test 3.3: Multiple clauses same weight - take first
!(println! "\n=== Test 3.3: WEIGHT - same weight ===")
!(let $queue (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
              (cons-atom (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
                         ()))
  (let $selected (select-clause-weight $queue)
    (case $selected
      (((Selected $clause $remaining)
        (if (== $clause (Clause (((⩳ (Fun P ((Fun a ()))) true) true))))
            (println! "✅ WEIGHT: same weight, selected first (P(a))")
            (println! "❌ Expected P(a) (first with same weight)")))
       ($_ (println! "❌ WEIGHT selection failed"))))))

;; Test 3.4: Prefer variables over constants in weight
;; P(X) (weight 2) has same weight as P(a) (weight 2)
!(println! "\n=== Test 3.4: WEIGHT - variables same as constants ===")
!(let $c1 (Clause (((⩳ (Fun P ((Var X))) true) true)))
  (let $c2 (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
    (if (== (clause-weight $c1) (clause-weight $c2))
        (println! "✅ P(X) and P(a) have same weight")
        (println! "❌ Variables should count same as constants"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 4: Queue Operations (3 tests)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 4.1: Add clause to queue
!(println! "\n=== Test 4.1: Add clause to queue ===")
!(let $queue (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                        ())
  (let $new-clause (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
    (let $new-queue (add-clause-to-queue $new-clause $queue)
      (if (== (list-length $new-queue) 2)
          (println! "✅ Added clause to queue")
          (println! "❌ Failed to add clause")))))

;; Test 4.2: Add multiple clauses (generated inferences)
!(println! "\n=== Test 4.2: Add multiple clauses ===")
!(let $queue (cons-atom (Clause (((⩳ (Fun P ((Fun a ()))) true) true)))
                        ())
  (let $new-clauses (cons-atom (Clause (((⩳ (Fun Q ((Fun b ()))) true) true)))
                     (cons-atom (Clause (((⩳ (Fun R ((Fun c ()))) true) true)))
                                ()))
    (let $new-queue (add-clauses-to-queue $new-clauses $queue)
      (if (== (list-length $new-queue) 3)
          (println! "✅ Added multiple clauses to queue")
          (println! "❌ Failed to add multiple clauses")))))

;; Test 4.3: Empty clause detection
;; Empty clause [] indicates UNSAT
!(println! "\n=== Test 4.3: Detect empty clause ===")
!(let $empty-clause (Clause ())
  (if (is-empty-clause $empty-clause)
      (println! "✅ Detected empty clause (UNSAT)")
      (println! "❌ Failed to detect empty clause")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

!(println! "\n=================================================================")
!(println! "Phase 5 Test Suite Complete")
!(println! "  Section 1: Clause Weight Calculation (4 tests)")
!(println! "  Section 2: FIFO Selection (3 tests)")
!(println! "  Section 3: Weight-Based Selection (4 tests)")
!(println! "  Section 4: Queue Operations (3 tests)")
!(println! "  Total: 14 tests")
!(println! "=================================================================")
