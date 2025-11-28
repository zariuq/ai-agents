;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; TPTP FOF to MeTTa - Generated via S-expression
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Nat for depth control
(: Nat Type)
(: Z Nat)
(: S (-> Nat Nat))
(: fromNumber (-> Number Nat))
(= (fromNumber $n) (if (<= $n 0) Z (S (fromNumber (- $n 1)))))

;;; Knowledge Base (Facts)
!(bind! &kb (new-space))

;; axiom2
!(add-atom &kb (human socrates))

;;; Rule Base (Inference Rules)
!(bind! &rb (new-space))

;; axiom1
!(add-atom &rb (⊢ (human $X) (mortal $X)))

;;; Backward Chainer
(: bc (-> Atom Nat Atom))

;; Base case: match goal against KB
(= (bc $goal Z)
   (match &kb $goal $goal))

;; Recursive case: apply rule from RB
(= (bc $goal (S $k))
   (match &rb
     (⊢ $premise $goal)
     (let $premise (bc $premise $k)
       $goal)))

;;; Query (Prove the conjecture)
; Proving: goal
!(bc (mortal socrates) (fromNumber 5))
