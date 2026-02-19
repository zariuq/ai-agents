;;; pverify_hybrid.metta - Hybrid Prolog+PeTTa Metamath Verifier
;;; Uses Prolog parser (one call), processes tuples in PeTTa
;;;
;;; Architecture:
;;;   1. Prolog parses .mm file into structured lists
;;;   2. PeTTa processes statements and calls verification functions
;;;   3. No file generation - pure in-memory integration
;;;
;;; mmverify-utils_petta imports lib_he and lib_prolog, so we don't import them here

!(import! &self ../mmverify/mmverify-utils_petta)

;; Compatibility override for upstream lib_he: ensure unify evaluates branches.
;; This matches the atps behavior used by existing mmverify/pverify scripts.
(= (unify $space $pattern $then $else)
   (if (is-space $space)
       (let $temp (cut)
            (case (match $space $pattern $pattern)
                  (($pattern (eval $then))
                   (Empty (eval $else))))) (empty)))

;;; get-first-non-flag-arg - Get the first command line argument that doesn't start with --
;;; Returns Empty if no non-flag arguments found
(= (get-first-non-flag-arg $idx)
   (let $arg (get_cmdline_arg $idx)
     (if (== $arg Empty)
         Empty
         ;; Check if arg starts with -- by using Prolog's is_flag_arg
         (let $is_flag (collapse (is_flag_arg $arg))
           (if (== (car-atom $is_flag) true)
               (get-first-non-flag-arg (+ $idx 1))
               $arg)))))

!(import_prolog_functions_from_file "../metamath/pverify/mm_primitives.pl"
  (parse_mm_file halt_with_code))
!(import_prolog_functions_from_file "../metamath/pverify/env_utils.pl"
  (get_env_var_or_default is_flag_arg))

;;; Initialize State
!(bind! &sp (new-state -1))  ; Stack pointer starts at -1 (increments to 0 on first push)
!(bind! &fd (new-state 0))
!(push-frame &fd)

;;; Note: printif! is defined in mmverify-utils_petta.metta based on --log flag

;;; ==========================================================================
;;; Process Statements Using decons-atom
;;; ==========================================================================

;; filter-errors - Extract Error atoms from results
(= (filter-errors $results)
   (if (== (size-atom $results) 0)
       ()
       (let ($first $rest) (decons-atom $results)
         (case $first
           (((Error $info $msg)
              (cons-atom $first (filter-errors $rest)))
            ($_ (filter-errors $rest)))))))

;; process-statements - Process tuple using map-atom (avoids recursion non-determinism)
;; Returns (ok) or (failed) to indicate success/failure
(= (process-statements $stmts)
   (let $results (collapse (map-atom $stmts $stmt (process-statement $stmt)))
     (let $errors (filter-errors (car-atom $results))
       (if (> (size-atom $errors) 0)
           (failed)
           (progn
             (printif! "=== All statements processed ===")
             (ok))))))



;;; ==========================================================================
;;; Statement Processing using decons-atom
;;; Statements are now lists: (c symbols) (v vars) (f label type var) etc.
;;; ==========================================================================

(= (process-statement $stmt)
   (let ($tag $data) (decons-atom $stmt)
     (process-by-tag $tag $data)))

(= (process-by-tag c $rest)
   (let ($symbols $_) (decons-atom $rest)
     (progn
       (printif! (Processing c statement with (size-atom $symbols) symbols))
       (process-c-symbols $symbols))))

(= (process-by-tag v $rest)
   (let ($vars $_) (decons-atom $rest)
     (progn
       (printif! (Processing v statement with (size-atom $vars) vars))
       (process-v-symbols $vars))))

(= (process-by-tag f $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($var $_) (decons-atom $rest3)
         (let $level (get-state &fd)
           (progn
             (printif! (Processing f: $label $type $var))
             (add_f &kb $label $type $var $level)))))))

(= (process-by-tag e $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $_) (decons-atom $rest3)
         (let $level (get-state &fd)
           (progn
             (printif! (Processing e: $label))
             (add_e &kb $label (cons-atom $type $math) $level)))))))

(= (process-by-tag a $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $_) (decons-atom $rest3)
         (progn
           (printif! (Processing a: $label))
           (add_a &kb $label (cons-atom $type $math)))))))

;; Helper to handle proof verification result.
;; Use case dispatch to remain parser-compatible across PeTTa variants.
(= (unwrap-singletons3 $x)
   (if (== (size-atom $x) 1)
       (let $x1 (car-atom $x)
         (if (== (size-atom $x1) 1)
             (let $x2 (car-atom $x1)
               (if (== (size-atom $x2) 1)
                   (car-atom $x2)
                   $x2))
             $x1))
       $x))

(= (handle-proof-result $res)
   (let $norm (unwrap-singletons3 $res)
     (case $norm
       (((Error $info $msg)
          (progn
            (println! "")
            (println! "=== VERIFICATION FAILED ===")
            (println! ("Error" $info $msg))
            (halt_with_code 1)))
        (() ())
        ($_ ())))))

(= (process-by-tag p $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $rest4) (decons-atom $rest3)
         (let ($proof $_) (decons-atom $rest4)
           (progn
             (printif! (Processing p: $label))
             (let $result (add_p &kb &stack &sp $label (cons-atom $type $math) $proof True)
               (handle-proof-result $result))))))))

(= (process-by-tag d $rest)
   (let ($vars $_) (decons-atom $rest)
     (let $level (get-state &fd)
       (progn
         (printif! (Processing d statement at level $level))
         (add_d &kb $vars $level)))))

(= (process-by-tag open_frame $_)
   (progn
     (printif! "Processing {")
     (push-frame &fd)))

(= (process-by-tag close_frame $_)
   (progn
     (printif! "Processing }")
     (pop-frame &kb &fd)))

;; process-c-symbols - Process tuple of c symbols
(= (process-c-symbols $symbols)
   (process-symbols $symbols add_c))

;; process-v-symbols - Process tuple of v symbols
(= (process-v-symbols $vars)
   (process-symbols $vars add_v_wrapper))

(= (process-symbols $syms $func)
   (if (== (size-atom $syms) 0)
       Empty
       (let ($first $rest) (decons-atom $syms)
         (progn
           ($func &kb $first)
           (process-symbols $rest $func)))))

(= (add_v_wrapper $kb $var)
   (let $level (get-state &fd)
     (add_v $kb $var $level)))

;; normalize-parse-output - Handle runtime-dependent nesting depth from parse bridge.
;; Expected final shape: list of statements.
(= (normalize-parse-output $x)
   (if (== (size-atom $x) 1)
       (let $inner (car-atom $x)
         (if (== (size-atom $inner) 0)
             $x
             (let $head (car-atom $inner)
               (if (> (size-atom $head) 1)
                   (normalize-parse-output $inner)
                   $x))))
       $x))

;;; ==========================================================================
;;; Main
;;; ==========================================================================

!(printif! "")
!(printif! "=== Hybrid Prolog+PeTTa Metamath Verifier ===")
!(printif! "")

!(printif! "Step 1: Get input file...")
;;; Use collapse to force deterministic execution (avoid running multiple times)
!(let $result
   (collapse
     (let $cmdline_arg (get-first-non-flag-arg 0)
       (let $input_file (if (== $cmdline_arg Empty)
                            (get_env_var_or_default "MM_INPUT_FILE" "../metamath/mmverify/tests/demo0.mm")
                            $cmdline_arg)
         (let true (printif! (concat "  File: " $input_file))
           (let true (printif! "Step 2: Parse file using Prolog...")
             (let $stmts_raw (collapse (parse_mm_file $input_file))
             (if (== (size-atom $stmts_raw) 0)
                  (progn
                    (println! "")
                    (println! "=== PARSE FAILED ===")
                    (failed))
                  (let $stmts (normalize-parse-output $stmts_raw)
                    (let true (printif! (Got (size-atom $stmts) statements))
                      (let true (printif! "")
                        (let true (printif! "Step 3: Process statements in PeTTa...")
                          (let $status (process-statements $stmts)
                            (case $status
                              ((failed (failed))
                               ((ok) (ok))))))))))))))))
   (if (== $result ())
       Empty
       (case (car-atom $result)
         (((failed) (halt_with_code 1))
          ($_ Empty)))))

!(printif! "")
!(printif! "Step 4: Close outer frame...")
!(pop-frame &kb &fd)

!(println! "")
!(println! "=== Verification Complete ===")
