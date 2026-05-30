; Narrow PeTTa compatibility helpers for HE-targeted translated files.
; Only surfaces that are genuinely PeTTa-specific and absent from current
; HE/CeTTa stdlib coverage belong here.
; Translated files import this as the sibling module `lib_petta`.

(: petta-lambda (-> Atom $t (-> $a $t)))
(= ((petta-lambda $var $body) $arg)
  (let $var $arg $body))

(: petta-apply1 (-> Atom Atom Atom))
(= (petta-apply1 (petta-lambda $var $body) $arg)
  (let $var $arg $body))
(= (petta-apply1 $f $arg)
  (if (== $f +)
    (petta-lambda $x (+ $arg $x))
    (function
      (chain (eval (atom-subst $f $fun ($fun $arg))) $call
        (chain (eval $call) $mid
          (chain (eval $mid) $res
            (return $res)))))))

(: petta-apply2 (-> Atom Atom Atom Atom))
(= (petta-apply2 $f $arg1 $arg2)
  (if (== $f +)
    (+ $arg1 $arg2)
    (petta-apply1 (petta-apply1 $f $arg1) $arg2)))

(: petta-ffi-function-call-inversion (-> Atom Atom Atom Atom Atom))
(= (petta-ffi-function-call-inversion $lane $pattern $observed $continuation)
  (Error (petta-ffi-function-call-inversion $lane $pattern $observed $continuation)
         "ffi token required for function-call inversion"))

(: petta-normalize-results (-> Atom Atom))
(= (petta-normalize-results $tuple)
  (case $tuple
    ((($single) $single)
     ($many $many))))

(: petta-test-equal (-> Atom Atom Bool))
(= (petta-test-equal $actual $expected)
  (let $actual-value $actual
    (if (== $actual-value $expected)
      (let $printed
        (println! (format-args "is {}, should {}. ✅" ($actual-value $expected)))
        True)
      (if (=alpha $actual-value $expected)
        (let $printed
          (println! (format-args "is {}, should {}. ✅" ($actual-value $expected)))
          True)
        (let $printed
          (println! (format-args "is {}, should {}. ❌" ($actual-value $expected)))
          False)))))

(: petta-test-results (-> Atom Atom Bool))
(= (petta-test-results $actual $expected)
  (let $actual-results (petta-normalize-results (collapse $actual))
    (let $expected-results (petta-normalize-results (collapse $expected))
      (if (== $actual-results $expected-results)
        (let $printed
          (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
          True)
        (let $printed
          (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
          False)))))

(: petta-test-bag-equal (-> Atom Atom Bool))
(= (petta-test-bag-equal $actual $expected)
  (let $actual-results (collapse (let $actual-item $actual $actual-item))
    (let $expected-results $expected
      (let $actual-only (subtraction-atom $actual-results $expected-results)
        (let $expected-only (subtraction-atom $expected-results $actual-results)
          (if (== $actual-only ())
            (if (== $expected-only ())
              (let $printed
                (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
                True)
              (let $printed
                (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
                False))
            (let $printed
              (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
              False)))))))

(: is-member (-> Atom Atom Bool))
(= (is-member $item $tuple)
  (not (== (collapse (let $x (superpose $tuple)
                         (if (== $x $item)
                             True
                             (empty))))
           ())))

(: second-from-pair (-> Atom Atom))
(= (second-from-pair $pair)
  (function
    (unify $pair ($first $second)
      (return $second)
      (return (Error (second-from-pair $pair) "incorrect pair format")))))
