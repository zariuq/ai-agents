;;; pverify_hybrid.metta - Hybrid Prolog+PeTTa Metamath Verifier
;;; Uses Prolog parser (one call), processes tuples in PeTTa
;;;
;;; Architecture:
;;;   1. Prolog parses .mm file into structured lists
;;;   2. PeTTa processes statements and calls verification functions
;;;   3. No file generation - pure in-memory integration
;;;
;;; Import order is critical - lib_he FIRST, then pverify-utils!
;;; pverify-utils has lib_he import commented out to avoid double-import

!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_he)
!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_prolog)
; !(import! &self pverify-utils)
!(import! &self mmverify-utils_petta)


;;; Import halt for proper exit code handling
!(import_prolog_function halt)

!(import_prolog_functions_from_file "/home/zar/claude/hyperon/metamath/pverify/mm_primitives.pl"
  (parse_mm_file))
!(import_prolog_functions_from_file "/home/zar/claude/hyperon/metamath/pverify/env_utils.pl"
  (get_env_var_or_default))

;;; Initialize State
!(bind! &sp (new-state -1))  ; Stack pointer starts at -1 (increments to 0 on first push)
!(bind! &fd (new-state 0))
!(push-frame &fd)

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
   (let $results (map-atom $stmts $stmt (process-statement $stmt))
     (let $errors (filter-errors $results)
       (if (> (size-atom $errors) 0)
           (failed)
           (progn
             (println! "=== All statements processed ===")
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
       (println! (Processing c statement with (size-atom $symbols) symbols))
       (process-c-symbols $symbols))))

(= (process-by-tag v $rest)
   (let ($vars $_) (decons-atom $rest)
     (progn
       (println! (Processing v statement with (size-atom $vars) vars))
       (process-v-symbols $vars))))

(= (process-by-tag f $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($var $_) (decons-atom $rest3)
         (progn
           (println! (Processing f: $label $type $var))
           (add_f &kb $label $type $var 1))))))

(= (process-by-tag e $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $_) (decons-atom $rest3)
         (progn
           (println! (Processing e: $label))
           (add_e &kb $label (cons-atom $type $math) 2))))))

(= (process-by-tag a $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $_) (decons-atom $rest3)
         (progn
           (println! (Processing a: $label))
           (add_a &kb $label (cons-atom $type $math)))))))

(= (process-by-tag p $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $rest4) (decons-atom $rest3)
         (let ($proof $_) (decons-atom $rest4)
           (progn
             (println! (Processing p: $label))
             (let $results (collapse (add_p &kb &stack &sp $label (cons-atom $type $math) $proof True))
               (let $result (if (== (size-atom $results) 0) () (car-atom $results))
                   (case $result
                 (((Error $info $msg)
                    (progn
                      (println! "")
                      (println! "=== VERIFICATION FAILED ===")
                      (println! "Terminating verification.")
                      (println! ("On error:" $info $msg))
                      $result))
                  (() Empty)))))))))))


(= (process-by-tag d $rest)
   (let ($vars $_) (decons-atom $rest)
     (let $level (get-state &fd)
       (progn
         (println! (Processing d statement at level $level))
         (add_d &kb $vars $level)))))

(= (process-by-tag open_frame $_)
   (progn
     (println! "Processing {")
     (push-frame &fd)))

(= (process-by-tag close_frame $_)
   (progn
     (println! "Processing }")
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
   (add_v $kb $var 1))

;;; ==========================================================================
;;; Main
;;; ==========================================================================

!(println! "")
!(println! "=== Hybrid Prolog+PeTTa Metamath Verifier ===")
!(println! "")

!(println! "Step 1: Get input file...")
!(let $cmdline_arg (get_cmdline_arg 0)
  (let $input_file (if (== $cmdline_arg Empty)
                       (get_env_var_or_default "MM_INPUT_FILE" "/home/zar/claude/hyperon/metamath/mmverify/tests/demo0.mm")
                       $cmdline_arg)
    (let true (println! (concat "  File: " $input_file))
      (let true (println! "Step 2: Parse file using Prolog...")
        (let $stmts (parse_mm_file $input_file)
          (let true (println! (Got (size-atom $stmts) statements))
            (let true (println! "")
              (let true (println! "Step 3: Process statements in PeTTa...")
                (let $status (process-statements $stmts)
                  (case $status
                    ((failed
                       (callPredicate (Predicate (halt 1))))
                     ((ok) Empty))))))))))))

!(println! "")
!(println! "Step 4: Close outer frame...")
!(pop-frame &kb &fd)

!(println! "")
!(println! "=== Verification Complete ===")
