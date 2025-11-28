;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Correct Backward Chainer Rules for boole-thm-7
;;;
;;; Rules are assertions, not equations!
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types
(: Object Type)
(: Set Type)

;; Predicates
(: in (-> Object Set Bool))
(: non-empty (-> Set Bool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Knowledge Base (Facts)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: a Object)
(: b Object)
(: mySet Set)

;; Facts: what's in the knowledge base
(in a mySet)
(in b mySet)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Backward Chaining Rules
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rule: If we can find an element in X, then X is non-empty
;; This is the DEFINITION from XBOOLE_0:def 1
;;
;; Backward: To prove (non-empty $X), prove (in $witness $X)

(: bc-non-empty-by-witness (-> $t $t Bool))
(bc-non-empty-by-witness $witness $X)
(if (in $witness $X)
    (non-empty $X)
    Empty)

;; Alternative notation: as an implication
;; (: implies (-> Bool Bool Bool))
;; (implies (in $x $X) (non-empty $X))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Chainer Query Format
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; To query with backward chainer:
;;
;; Goal: (non-empty mySet)
;;
;; Chainer looks for rules with head matching (non-empty $X)
;; Finds: bc-non-empty-by-witness
;; Generates subgoal: (in $witness mySet)
;; Searches KB for: (in $witness mySet)
;; Finds: (in a mySet)
;; Binds: $witness = a
;; Returns: Success with proof

;; For hyperon chainer, we need:
;; (bc (non-empty mySet))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Test Queries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Direct check: is 'a' in mySet?
!(match &self (in a mySet) $x)
;; Expected: [(in a mySet)]

;; Can we derive non-empty?
!(match &self (in $x mySet)
   (non-empty mySet))
;; Expected: [(non-empty mySet)]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Correct Rule Format for MeTTa Chainer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rules should be in the space, not as equations
;; The chainer searches the space for patterns

;; Format 1: As a conditional assertion
(: rule1 (-> $t $t Type))
(: apply-rule1 (-> $t $t))
(apply-rule1 $x $X)
(match &self (in $x $X)
  (non-empty $X))

;; Format 2: Using if-then structure (for chainer to process)
;; This is what the chainer actually needs to see

;; The rule in logical form:
;; ∀x,X. (x ∈ X) → (X is non-empty)

;; In MeTTa chainer format:
;; (rule
;;   (non-empty $X)      ; head (what we want to prove)
;;   (in $witness $X))   ; body (what we need to prove to get head)

