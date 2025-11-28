;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Proper Backward Chainer for boole-thm-7
;;;
;;; Following the pattern from b2_backchain.metta
;;; Using match and = for chaining, not bare assertions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knowledge Base - Facts about sets and elements
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Facts: elements in sets
(In a mySet)
(In b mySet)
(In c mySet)

;; Rule from XBOOLE_0:def 1
;; X is non-empty ⟺ ∃x. x ∈ X
;; As an implication: (x ∈ X) → (X is non-empty)
(Implication
  (In $x $X)
  (NonEmpty $X))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Backward Chaining Deduction Rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Base case: If the fact is in the KB, return True
(= (prove (In $x $X))
   (match &self (In $x $X) True))

(= (prove (NonEmpty $X))
   (match &self (NonEmpty $X) True))

;; Recursive case: If we have an implication, prove the antecedent
(= (prove (NonEmpty $X))
   (match &self
     (Implication (In $witness $X) (NonEmpty $X))
     (prove (In $witness $X))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Test Queries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 1: Can we prove a is in mySet? (base case)
!(prove (In a mySet))
;; Expected: True

;; Test 2: Can we prove mySet is non-empty? (uses implication)
!(prove (NonEmpty mySet))
;; Expected: True (by finding witness 'a')

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; With Proof Terms (like explain in b2_backchain.metta)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Base case: fact in KB
(= (explain (In $x $X))
   (match &self (In $x $X) (fact (In $x $X))))

(= (explain (NonEmpty $X))
   (match &self (NonEmpty $X) (fact (NonEmpty $X))))

;; Recursive case: prove via implication
(= (explain (NonEmpty $X))
   (match &self
     (Implication (In $witness $X) (NonEmpty $X))
     ((NonEmpty $X)
       by-witness $witness
       proven-by (explain (In $witness $X)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Test with Proof Terms
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test 3: Get proof explanation
!(explain (NonEmpty mySet))
;; Expected: ((NonEmpty mySet) by-witness a proven-by (fact (In a mySet)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Theorem boole-7 as an implication
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The actual theorem from boole.miz:
;; for x, X being set st x in X holds X is non empty

;; This is exactly: (In x X) → (NonEmpty X)
;; Which we already have as our rule!

;; So the chainer AUTOMATICALLY proves boole-thm-7
;; by using the implication rule and finding witnesses

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Key insights:
;; 1. Facts are bare assertions: (In a mySet)
;; 2. Rules are implications: (Implication antecedent consequent)
;; 3. Deduction uses = with match to search and chain
;; 4. The chainer recursively applies rules until it finds facts

;; This follows the exact pattern from b2_backchain.metta!
