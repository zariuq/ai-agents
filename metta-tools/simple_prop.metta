;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; TPTP to MeTTa - Generated Backward Chainer Code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Nat for depth control
(: Nat Type)
(: Z Nat)
(: S (-> Nat Nat))
(: fromNumber (-> Number Nat))
(= (fromNumber $n) (if (<= $n 0) Z (S (fromNumber (- $n 1)))))

;;; Knowledge Base (Facts)
!(bind! &kb (new-space))

;; fact_p
!(add-atom &kb p)

;;; Rule Base (Inference Rules)
!(bind! &rb (new-space))

;; fact_impl
!(add-atom &rb (⊢ p q))

;;; Backward Chainer (Nil's pattern)
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
! "=== Proving goal ==="
!(bc q (fromNumber 5))

;; Expected: q