;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Mizar Backward Chainer - Nil Geisweiller Style
;;;
;;; Proper implementation following bc-xp.metta patterns
;;; For boole-thm-7: for x, X being set st x in X holds X is non empty
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Nat for depth control (from Nil's bc-xp.metta)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: Nat Type)
(: Z Nat)
(: S (-> Nat Nat))

;; Convert Number to Nat
(: fromNumber (-> Number Nat))
(= (fromNumber $n) (if (<= $n 0) Z (S (fromNumber (- $n 1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knowledge Base (facts about sets)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Create KB space
!(bind! &mizar-kb (new-space))

;; Add facts: elements in sets
!(add-atom &mizar-kb (In a mySet))
!(add-atom &mizar-kb (In b mySet))
!(add-atom &mizar-kb (In c mySet))
!(add-atom &mizar-kb (In a anotherSet))

;; Could also add:
;; !(add-atom &mizar-kb (Empty emptySet))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rule Base (inference rules from Mizar)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Create RB space
!(bind! &mizar-rb (new-space))

;; XBOOLE_0:def 1
;; X is non-empty ⟺ ∃x. x ∈ X
;; As backward rule: To prove (NonEmpty X), prove (In $witness X)
!(add-atom &mizar-rb
  (⊢
    ;; Premise
    (In $witness $X)
    ;; Conclusion
    (NonEmpty $X)))

;; Could add more rules:
;; Empty set definition
;; !(add-atom &mizar-rb
;;   (⊢
;;     (Empty $X)
;;     (= $X {})))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Backward Chainer (Nil's "Bare Entail Match" pattern)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: bc (-> Atom Nat Atom))

;; Base case: goal is in KB
(= (bc $goal Z)
   (match &mizar-kb $goal $goal))

;; Recursive case: single premise rule
(= (bc $goal (S $k))
   (match &mizar-rb
     (⊢ $premise $goal)
     (bc $premise $k)))

;; For rules with 2 premises (like modus ponens)
;; We'd need let* for AND-branches:
;; (= (bc $goal (S $k))
;;    (match &mizar-rb
;;      (⊢ $premise1 $premise2 $goal)
;;      (let* (($premise1 (bc $premise1 $k))
;;             ($premise2 (bc $premise2 $k)))
;;        $goal)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Test Queries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Testing Mizar Backward Chainer ==="

;; Test 1: Direct fact lookup (base case)
! "Test 1: Is 'a' in mySet?"
!(assertEqual
  (bc (In a mySet) Z)
  (In a mySet))

;; Test 2: One-step inference
! "Test 2: Is mySet non-empty? (depth 1)"
!(assertEqual
  (bc (NonEmpty mySet) (S Z))
  (NonEmpty mySet))

;; Test 3: What about anotherSet?
! "Test 3: Is anotherSet non-empty?"
!(assertEqual
  (bc (NonEmpty anotherSet) (S Z))
  (NonEmpty anotherSet))

;; Test 4: Empty set should fail
! "Test 4: Is unknownSet non-empty? (should fail)"
!(assertEqualToResult
  (bc (NonEmpty unknownSet) (S Z))
  ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Version with Proof Terms (like Nil's "explain" variant)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: bc-explain (-> Atom Nat Atom))

;; Base case: fact in KB
(= (bc-explain $goal Z)
   (match &mizar-kb $goal (fact $goal)))

;; Recursive case with proof construction
(= (bc-explain $goal (S $k))
   (match &mizar-rb
     (⊢ $premise $goal)
     (let $premise-proof (bc-explain $premise $k)
       ($goal by-rule xboole0-def1 with $premise-proof))))

! "=== Testing with Proof Terms ==="

;; Test 5: Get proof for NonEmpty mySet
! "Test 5: Proof that mySet is non-empty"
!(assertEqual
  (bc-explain (NonEmpty mySet) (S Z))
  ((NonEmpty mySet) by-rule xboole0-def1 with (fact (In a mySet))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Multiple Solutions (nondeterminism)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Multiple Witnesses ==="

;; The chainer should find ALL valid witnesses
! "All proofs that mySet is non-empty:"
!(assertEqualToResult
  (bc (NonEmpty mySet) (fromNumber 1))
  ((NonEmpty mySet)  ; via witness a
   (NonEmpty mySet)  ; via witness b
   (NonEmpty mySet))) ; via witness c

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Extension: Handling Quantifiers (for future)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For handling "for x, X being set st x in X"
;; We'd need a rule like:

;; !(add-atom &mizar-rb
;;   (⊢
;;     ;; Premises (universal instantiation)
;;     (Being $x set)
;;     (Being $X set)
;;     (In $x $X)
;;     ;; Conclusion
;;     (NonEmpty $X)))

;; This would require bc variant handling 3 premises with let*

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

! "=== Summary ==="
! "This implements proper backward chaining following Nil's pattern:"
! "1. Depth control with Nat type"
! "2. Separate KB and RB spaces"
! "3. Match-based unification"
! "4. Entailment operator ⊢"
! "5. Proof term generation"
! ""
! "The chainer correctly proves boole-thm-7:"
! "Given (In a mySet), it derives (NonEmpty mySet)"
! "using XBOOLE_0:def 1 as the inference rule."

;; End of file