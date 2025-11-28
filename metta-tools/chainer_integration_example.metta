;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Backward Chainer Integration Example
;;;
;;; Shows how to use MeTTa's backward chainer to prove boole-thm-7
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types
(: Object Type)
(: Set Type)

;; Basic predicates
(: in (-> Object Set Bool))
(: non-empty (-> Set Bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knowledge Base (Facts)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Objects in our domain
(: a Object)
(: b Object)
(: c Object)

;; A non-empty set
(: mySet Set)
(= (in a mySet) True)
(= (in b mySet) True)

;; An empty set
(: emptySet Set)
(= (in $x emptySet) False)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rules for Backward Chaining
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rule 1: To prove (non-empty X), find witness w such that (in w X)
;; This is the KEY rule from XBOOLE_0:def 1

(: rule-non-empty-by-witness (-> Set Object Bool))
(= (rule-non-empty-by-witness $X $witness)
   (if (in $witness $X)
       (non-empty $X)
       False))

;; Rule 2: Theorem boole-7 as a rule
;; Given x ∈ X, conclude X is non-empty

(: rule-boole-thm-7 (-> Object Set Bool))
(= (rule-boole-thm-7 $x $X)
   (if (in $x $X)
       (non-empty $X)
       False))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Backward Chainer Queries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Query 1: Is mySet non-empty?
;; Expected: Chainer should find witness 'a' from KB

!(rule-boole-thm-7 a mySet)
;; Output: (non-empty mySet)

;; Query 2: Try with explicit witness
!(rule-non-empty-by-witness mySet a)
;; Output: (non-empty mySet)

;; Query 3: Empty set should fail
!(rule-boole-thm-7 a emptySet)
;; Output: False (because (in a emptySet) = False)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Proof Search Example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Simulated backward chainer logic:
;;
;; Goal: (non-empty mySet)
;;
;; Step 1: Match against rule heads
;;   - rule-non-empty-by-witness has conclusion (non-empty $X)
;;   - Unify: $X = mySet
;;
;; Step 2: New subgoal from rule body
;;   - Need: (in $witness mySet) for some $witness
;;
;; Step 3: Search KB for facts matching (in $witness mySet)
;;   - Found: (in a mySet) = True
;;   - Unify: $witness = a
;;
;; Step 4: Subgoal satisfied
;;   - Return: (non-empty mySet) = True
;;   - Proof: by witness 'a'
;;
;; QED ✓

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; With Proof Terms (Optional)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define proof term type
(: Proof Type)
(: by-witness (-> Object Set Proof))
(: by-rule (-> String Proof Proof))

;; Generate proof term
(: prove-with-term (-> Object Set Proof))
(= (prove-with-term $x $X)
   (if (in $x $X)
       (by-witness $x $X)
       (empty-proof)))

;; Test proof term generation
!(prove-with-term a mySet)
;; Expected: (by-witness a mySet)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Integration with Hyperon Chainer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To use with hyperon's backward chainer:
;;
;; 1. Import chainer module:
;;    (import! &chainer)
;;
;; 2. Define rules in chainer format:
;;    (add-rule! &kb
;;      (rule
;;        (non-empty $X)
;;        (in $witness $X)))
;;
;; 3. Add facts to KB:
;;    (add-fact! &kb (in a mySet))
;;    (add-fact! &kb (in b mySet))
;;
;; 4. Query:
;;    (bc-query &kb (non-empty mySet))
;;
;; 5. Chainer will:
;;    - Try rule with goal (non-empty mySet)
;;    - Generate subgoal (in $witness mySet)
;;    - Search KB for matching fact
;;    - Find (in a mySet)
;;    - Unify and return success with binding {$witness: a}

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Summary
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This file demonstrates:
;; 1. ✓ Knowledge base with facts
;; 2. ✓ Rules for backward chaining
;; 3. ✓ Query evaluation
;; 4. ✓ Witness instantiation
;; 5. ✓ Proof term generation
;; 6. ✓ Integration path with hyperon chainer

;; Next steps:
;; - Hook up actual hyperon chainer
;; - Add more rules (transitivity, extensionality)
;; - Import full boole.miz definitions
;; - Automate proof search

;; End of file
