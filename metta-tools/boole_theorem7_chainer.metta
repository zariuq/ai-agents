;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; MeTTa Chainer Rules for boole-thm-7
;;;
;;; Theorem: for x, X being set st x in X holds X is non empty
;;; Proof: by XBOOLE_0:def 1
;;;
;;; This is the SIMPLEST possible Mizar verification - just witness
;;; instantiation!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Import the S-expression representation
;; (forall (("x" "X" (mode 0 "set")))
;;   (such-that
;;     (pred-infix + 2 "in" (var "x") (var "X")))
;;     (attr + (var "X") ((non ((attr 1 "empty"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Definitions (from XBOOLE_0)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; XBOOLE_0:def 1 - Definition of "empty"
;; Mizar: attr X is empty means not ex x st x in X;
;;
;; In logic: empty(X) ⟺ ¬∃x. x ∈ X
;; Contrapositive: non-empty(X) ⟺ ∃x. x ∈ X

(: empty (-> $t Bool))
(= (empty $X)
   (not (exists $x (in $x $X))))

(: non-empty (-> $t Bool))
(= (non-empty $X)
   (exists $x (in $x $X)))

;; Equivalence between the forms
(: empty-iff (-> $t Bool))
(= (empty-iff $X)
   (iff (empty $X) (not (non-empty $X))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Backward Chaining Rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rule 1: Witness introduction
;; If we have (in $x $X), we can prove (non-empty $X)
;; by providing $x as the witness for (exists $y (in $y $X))

(: bc-witness-for-non-empty (-> $t $t Bool))
(= (bc-witness-for-non-empty $x $X)
   (let $witness $x
     (case (in $witness $X)
       ((True (non-empty $X))))))

;; Rule 2: Existential instantiation (constructive)
;; To prove (exists $y (in $y $X)), provide a witness

(: bc-exists-witness (-> $t $t Bool))
(= (bc-exists-witness $witness $X)
   (if (in $witness $X)
       (exists $y (in $y $X))
       False))

;; Rule 3: Definition unfolding
;; non-empty(X) = exists y. y in X

(: bc-unfold-non-empty (-> $t Bool))
(= (bc-unfold-non-empty $X)
   (if (non-empty $X)
       (exists $y (in $y $X))
       False))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Forward Chaining Rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rule 4: Forward - from membership to non-empty
;; If x ∈ X, then X is non-empty

(: fc-in-implies-non-empty (-> $t $t Bool))
(= (fc-in-implies-non-empty $x $X)
   (if (in $x $X)
       (non-empty $X)
       (nop)))

;; Rule 5: Forward - witness extraction
;; If we know (in $x $X), record it as evidence

(: fc-record-witness (-> $t $t (Witness $t $t)))
(= (fc-record-witness $x $X)
   (if (in $x $X)
       (Witness $x $X)
       (nop)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The Theorem (boole-thm-7)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Direct translation of the S-expression
(: boole-thm-7 (-> $t $t Bool))
(= (boole-thm-7 $x $X)
   (if (in $x $X)
       (non-empty $X)
       True))

;; Alternative: as a rule
(: prove-boole-thm-7 (-> $t $t (Proof non-empty)))
(= (prove-boole-thm-7 $x $X)
   (case (in $x $X)
     ((True (Proof
              (non-empty $X)
              (by-witness $x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Test Cases
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test data: concrete sets
(: a Object)
(: b Object)
(: c Object)

;; Define a set {a, b, c}
(: set-abc Set)
(= (in a set-abc) True)
(= (in b set-abc) True)
(= (in c set-abc) True)
(= (in $x set-abc) False)  ;; default: not in set

;; Test 1: Prove set-abc is non-empty
!(bc-witness-for-non-empty a set-abc)
;; Expected: (non-empty set-abc) = True

;; Test 2: Use the theorem directly
!(boole-thm-7 a set-abc)
;; Expected: True

;; Test 3: With proof term
!(prove-boole-thm-7 a set-abc)
;; Expected: (Proof (non-empty set-abc) (by-witness a))

;; Test 4: Empty set (should fail)
(: empty-set Set)
(= (in $x empty-set) False)

!(boole-thm-7 a empty-set)
;; Expected: True (vacuously - premise is False)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Chainer Integration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To use with a backward chainer:
;;
;; Goal: (non-empty $X)
;; Apply: bc-witness-for-non-empty
;; Subgoal: (in $witness $X)  [for some $witness]
;; Search: Find any fact (in $a $X) in knowledge base
;; Unify: $witness = $a
;; QED

;; Knowledge base example:
(: kb-fact-1 Fact)
(= kb-fact-1 (in a set-abc))

(: kb-fact-2 Fact)
(= kb-fact-2 (in b set-abc))

;; Query:
;; !(chain-backward (non-empty set-abc))
;;
;; Chainer should:
;; 1. Try bc-witness-for-non-empty
;; 2. Subgoal: (in $witness set-abc)
;; 3. Search KB: find kb-fact-1: (in a set-abc)
;; 4. Unify: $witness = a
;; 5. Return: True with witness=a
;; QED ✓

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Proof Object (Optional - for proof terms)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If we want to generate proof terms:

(: ProofTerm Type)
(: ByWitness (-> Object ProofTerm))
(: ByDef (-> String ProofTerm))
(: ApplyRule (-> String ProofTerm ProofTerm))

(: prove-with-term (-> $t $t ProofTerm))
(= (prove-with-term $x $X)
   (case (in $x $X)
     ((True
       (ApplyRule "boole-thm-7"
         (ByWitness $x))))))

;; Test with proof term
!(prove-with-term a set-abc)
;; Expected: (ApplyRule "boole-thm-7" (ByWitness a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This demonstrates:
;; 1. ✓ Definition translation (empty → not exists)
;; 2. ✓ Backward chaining (goal → subgoal)
;; 3. ✓ Witness instantiation (exists elimination)
;; 4. ✓ Simple theorem proving
;; 5. ✓ Proof term generation (optional)
;;
;; Next steps:
;; - Hook up to actual MeTTa chainer
;; - Add more complex rules (universal quantifiers)
;; - Import full boole.miz S-expressions
;; - Verify all 8 theorems automatically

;; End of file
