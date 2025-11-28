;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test Utilities for PeTTaRes Development
;; Works with both HE MeTTa and PeTTa
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test equality with output
;; Using conditional to avoid double firing
(= (test-eq $name $actual $expected)
   (if (== $actual $expected)
       (let* (($_ (println! ("✅" $name))))
         ())
       (let* (($_ (println! ("❌" $name "got:" $actual "expected:" $expected))))
         ())))
