; Narrow PeTTa compatibility helpers for HE-targeted translated files.
; Only surfaces that are genuinely PeTTa-specific and absent from current
; HE/CeTTa stdlib coverage belong here.
; Translated files import this as the sibling module `lib_petta`.

(: petta-lambda (-> Atom $t (-> $a $t)))
(= ((petta-lambda $var $body) $arg)
  (unquote (quote (let $var $arg $body))))

(: petta-apply1 (-> Atom Atom Atom))
(= (petta-apply1 (petta-lambda $var $body) $arg)
  (unquote (quote (let $var $arg $body))))
(= (petta-apply1 $f $arg)
  (eval ($f $arg)))

(: petta-apply2 (-> Atom Atom Atom Atom))
(= (petta-apply2 $f $arg1 $arg2)
  (let $__tr_apply_mid (petta-apply1 $f $arg1)
    (petta-apply1 $__tr_apply_mid $arg2)))

(: petta-ffi-function-call-inversion (-> Atom Atom Atom Atom Atom))
(= (petta-ffi-function-call-inversion $lane $pattern $observed $continuation)
  (Error (petta-ffi-function-call-inversion $lane $pattern $observed $continuation)
         "ffi token required for function-call inversion"))

(: petta-normalize-results (-> Atom Atom))
(= (petta-normalize-results $tuple)
  (petta-public-term
    (case $tuple
      ((($single) $single)
       ($many $many)))))

(: petta-public-term (-> Atom Atom))
(: petta-public-syntax (-> Atom Atom))
(= (petta-public-term $expr)
  (if (== (get-metatype $expr) Expression)
    (case $expr
      ((() ())
       ((quote $__tr_public_quoted)
        (petta-public-syntax $__tr_public_quoted))
       ($__tr_public_any
        (map-atom $expr $item (eval (petta-public-term $item))))))
    $expr))
(= (petta-public-syntax $expr)
  (if (== (get-metatype $expr) Expression)
    (case $expr
      ((() ())
       ($__tr_public_any
        (map-atom $expr $item (eval (petta-public-syntax $item))))))
    $expr))
(= (petta-if2 True $then) $then)

(: petta-test-equal (-> Atom Atom Bool))
(= (petta-test-equal $actual $expected)
  (let $actual-value (eval $actual)
    (let $expected-value (eval $expected)
      (let $actual-public-1 (eval (petta-public-term $actual-value))
        (let $expected-public-1 (eval (petta-public-term $expected-value))
          (let $actual-public (eval $actual-public-1)
            (let $expected-public (eval $expected-public-1)
          (if (== $actual-public $expected-public)
            (let $printed
              (println! (format-args "is {}, should {}. ✅" ($actual-public $expected-public)))
              True)
            (if (=alpha $actual-public $expected-public)
              (let $printed
                (println! (format-args "is {}, should {}. ✅" ($actual-public $expected-public)))
                True)
              (let $printed
                (println! (format-args "is {}, should {}. ❌" ($actual-public $expected-public)))
                False))))))))))

(: petta-test-equal-data (-> Atom Atom Bool))
(= (petta-test-equal-data $actual $expected)
  (let $actual-value (eval $actual)
    (case $expected
      (((quote $__tr_expected_syntax)
        (let $actual-public-1 (eval (petta-public-term $actual-value))
          (let $expected-public-1 (eval (petta-public-syntax $__tr_expected_syntax))
            (let $actual-public (eval $actual-public-1)
              (let $expected-public (eval $expected-public-1)
                (if (== $actual-public $expected-public)
                  (let $printed
                    (println! (format-args "is {}, should {}. ✅" ($actual-public $expected-public)))
                    True)
                  (if (=alpha $actual-public $expected-public)
                    (let $printed
                      (println! (format-args "is {}, should {}. ✅" ($actual-public $expected-public)))
                      True)
                    (let $printed
                      (println! (format-args "is {}, should {}. ❌" ($actual-public $expected-public)))
                      False))))))))
       ($__tr_expected_any
        (if (== $actual-value $__tr_expected_any)
          (let $printed
            (println! (format-args "is {}, should {}. ✅" ($actual-value $__tr_expected_any)))
            True)
          (if (=alpha $actual-value $__tr_expected_any)
            (let $printed
              (println! (format-args "is {}, should {}. ✅" ($actual-value $__tr_expected_any)))
              True)
            (let $actual-public-1 (eval (petta-public-term $actual-value))
              (let $expected-public-1 (eval (petta-public-term $__tr_expected_any))
                (let $actual-public (eval $actual-public-1)
                  (let $expected-public (eval $expected-public-1)
                    (if (== $actual-public $expected-public)
                      (let $printed
                        (println! (format-args "is {}, should {}. ✅" ($actual-public $expected-public)))
                        True)
                      (if (=alpha $actual-public $expected-public)
                        (let $printed
                          (println! (format-args "is {}, should {}. ✅" ($actual-public $expected-public)))
                          True)
                        (let $printed
                          (println! (format-args "is {}, should {}. ❌" ($actual-public $expected-public)))
                          False))))))))))))))

(: petta-test-results (-> Atom Atom Bool))
(= (petta-test-results $actual $expected)
  (let $__tr_actual_collapse (collapse (let $__tr_actual_item $actual $__tr_actual_item))
    (let $__tr_expected_collapse (collapse (let $__tr_expected_item $expected $__tr_expected_item))
      (let $actual-results-1 (eval (petta-normalize-results $__tr_actual_collapse))
        (let $expected-results-1 (eval (petta-normalize-results $__tr_expected_collapse))
          (let $actual-results (eval $actual-results-1)
            (let $expected-results (eval $expected-results-1)
              (if (== $actual-results $expected-results)
                (let $printed
                  (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
                  True)
                (let $printed
                  (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
                  False)))))))))

(: petta-test-results-data (-> Atom Atom Bool))
(= (petta-test-results-data $actual $expected)
  (let $__tr_actual_collapse (collapse (let $__tr_actual_item $actual $__tr_actual_item))
    (let $__tr_actual_results_raw $__tr_actual_collapse
      (case $expected
        (((quote $__tr_expected_syntax)
          (let $actual-results-1 (eval (petta-normalize-results $__tr_actual_collapse))
            (let $expected-results-1 (eval (petta-public-syntax $__tr_expected_syntax))
              (let $actual-results (eval $actual-results-1)
                (let $expected-results (eval $expected-results-1)
                  (if (== $actual-results $expected-results)
                    (let $printed
                      (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
                      True)
                    (let $printed
                      (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
                      False)))))))
         ($__tr_expected_any
          (let $__tr_expected_results_raw $__tr_expected_any
            (if (== $__tr_actual_results_raw $__tr_expected_results_raw)
              (let $printed
                (println! (format-args "is {}, should {}. ✅" ($__tr_actual_results_raw $__tr_expected_results_raw)))
                True)
              (if (=alpha $__tr_actual_results_raw $__tr_expected_results_raw)
                (let $printed
                  (println! (format-args "is {}, should {}. ✅" ($__tr_actual_results_raw $__tr_expected_results_raw)))
                  True)
                (if (== (get-metatype $__tr_actual_results_raw) Expression)
                  (if (== (get-metatype $__tr_expected_results_raw) Expression)
                    (let $__tr_actual_only
                      (subtraction-atom $__tr_actual_results_raw $__tr_expected_results_raw)
                      (let $__tr_expected_only
                        (subtraction-atom $__tr_expected_results_raw $__tr_actual_results_raw)
                        (if (== $__tr_actual_only ())
                          (if (== $__tr_expected_only ())
                            (let $printed
                              (println! (format-args "is {}, should {}. ✅" ($__tr_actual_results_raw $__tr_expected_results_raw)))
                              True)
                            (let $actual-results-1 (eval (petta-normalize-results $__tr_actual_collapse))
                              (let $expected-results-1 (eval (petta-public-term $__tr_expected_any))
                                (let $actual-results (eval $actual-results-1)
                                  (let $expected-results (eval $expected-results-1)
                                    (if (== $actual-results $expected-results)
                                      (let $printed
                                        (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
                                        True)
                                      (let $printed
                                        (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
                                        False)))))))
                          (let $actual-results-1 (eval (petta-normalize-results $__tr_actual_collapse))
                            (let $expected-results-1 (eval (petta-public-term $__tr_expected_any))
                              (let $actual-results (eval $actual-results-1)
                                (let $expected-results (eval $expected-results-1)
                                  (if (== $actual-results $expected-results)
                                    (let $printed
                                      (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
                                      True)
                                    (let $printed
                                      (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
                                      False))))))))
                    (let $actual-results-1 (eval (petta-normalize-results $__tr_actual_collapse))
                      (let $expected-results-1 (eval (petta-public-term $__tr_expected_any))
                        (let $actual-results (eval $actual-results-1)
                          (let $expected-results (eval $expected-results-1)
                            (if (== $actual-results $expected-results)
                              (let $printed
                                (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
                                True)
                              (let $printed
                                (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
                                False))))))
                  (let $actual-results-1 (eval (petta-normalize-results $__tr_actual_collapse))
                    (let $expected-results-1 (eval (petta-public-term $__tr_expected_any))
                      (let $actual-results (eval $actual-results-1)
                        (let $expected-results (eval $expected-results-1)
                          (if (== $actual-results $expected-results)
                            (let $printed
                              (println! (format-args "is {}, should {}. ✅" ($actual-results $expected-results)))
                              True)
                            (let $printed
                              (println! (format-args "is {}, should {}. ❌" ($actual-results $expected-results)))
                              False))))))))))))))))))

(: petta-test-bag-equal (-> Atom Atom Bool))
(= (petta-test-bag-equal $actual $expected)
  (let $actual-results-1 (eval (petta-public-term (collapse (let $actual-item $actual $actual-item))))
    (let $expected-results-1 (eval (petta-public-term $expected))
      (let $actual-results (eval $actual-results-1)
        (let $expected-results (eval $expected-results-1)
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
              False)))))))))

(= (petta-bool-and True $y) $y)
(= (petta-bool-and False $y) False)

(= (petta-bool-or True $y) True)
(= (petta-bool-or False $y) $y)

(= (petta-member $x ($x $tail)) True)
(= (petta-member $x ($head $tail)) (petta-member $x $tail))

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

(: reverse (-> Atom Atom))
(= (reverse $xs)
  (petta-reverse-acc $xs ()))
(= (petta-reverse-acc () $acc)
  $acc)
(= (petta-reverse-acc $xs $acc)
  (case (decons-atom $xs)
    ((($head $tail)
      (petta-reverse-acc $tail (cons-atom $head $acc))))))

(: last (-> Atom Atom))
(= (last $xs)
  (case (decons-atom $xs)
    ((($head ()) $head)
     (($head $tail) (last $tail)))))

(: foldl (-> Atom Atom Atom Atom))
(= (foldl $f $list $init)
  (foldl-atom $list $init $__tr_acc $__tr_item
    (eval ($f $__tr_item $__tr_acc))))

(: min (-> Number Number Number))
(= (min $a $b)
  (if (<= $a $b) $a $b))

(: max (-> Number Number Number))
(= (max $a $b)
  (if (<= $a $b) $b $a))

(: alpha-unique-atom (-> Atom Atom))
(= (petta-is-alpha-member $item $tuple)
  (not (== (collapse (let $x (superpose $tuple)
                         (if (=alpha $x $item)
                             True
                             (empty))))
           ())))
(= (alpha-unique-atom $tuple)
  (petta-alpha-unique-atom-loop $tuple ()))
(= (petta-alpha-unique-atom-loop () $seen)
  ())
(= (petta-alpha-unique-atom-loop $tuple $seen)
  (case (decons-atom $tuple)
    ((($head $tail)
      (if (petta-is-alpha-member $head $seen)
          (petta-alpha-unique-atom-loop $tail $seen)
          (let $rest (petta-alpha-unique-atom-loop $tail (cons-atom $head $seen))
            (cons-atom $head $rest)))))))
