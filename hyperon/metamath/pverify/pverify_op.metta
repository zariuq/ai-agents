;;; pverify_op.metta — Optimized PeTTa Metamath Verifier
;;; ALL verification logic in PeTTa; O(log n) data structures via Prolog FFI.
;;; Purely functional state threading — no &kb, &stack, &sp, etc.
;;;
;;; Architecture:
;;;   Prolog: file parsing (mm_primitives.pl) + data structures (pverify_ds.pl)
;;;   PeTTa:  ALL verification logic (treat_step, apply_subst, check_dvs, etc.)
;;;
;;; Usage:
;;;   cd /home/zar/claude/hyperon/PeTTa
;;;   ./run.sh ../metamath/pverify/pverify_op.metta --silent -- path/to/file.mm

;;; ========== Section 1: Imports + FFI ==========

!(import! &self ../../PeTTa/lib/lib_he)
!(import! &self ../../PeTTa/lib/lib_import)
!(import! &self ../../PeTTa/lib/lib_zar)
!(import_prolog_functions_from_file_pred "lib/lib_zar.pl"
  (get_cmdline_args get_cmdline_arg cmdline_arg_count has_cmdline_args))

!(import_prolog_functions_from_file "../metamath/pverify/pverify_ds.pl"
  (ds_empty_assoc ds_assoc_get ds_assoc_put
   ds_empty_ordset ds_ord_add ds_ord_member ds_ord_union ds_ord_subtract
   ds_ord_from_list
   ds_stmt_functor ds_stmt_arg
   ds_stmt_cons ds_stmt_head ds_stmt_tail ds_stmt_size
   ds_stmt_eq ds_stmt_concat ds_stmt_empty ds_stmt_from_args
   ds_make_dv_pairs ds_dv_key ds_pair_fst ds_pair_snd
   ds_filter_dvs_mandvars
   ds_length ds_nth0 ds_reverse
   ds_parse_mm))

!(import_prolog_functions_from_file "../metamath/pverify/env_utils.pl"
  (get_env_var_or_default is_flag_arg halt_with_code))

;;; ========== Section 2: State + Frame Operations ==========
;;;
;;; State = (state Constants FrameStack Labels)
;;;   Constants:  opaque Prolog ordset
;;;   FrameStack: MeTTa list of Frame tuples (top frame first)
;;;   Labels:     opaque Prolog assoc (label → entry)
;;;
;;; Frame = (frame Vars DVs FHyps FLabels EHyps)
;;;   Vars:     opaque Prolog ordset of active variables
;;;   DVs:      opaque Prolog ordset of X-Y pairs
;;;   FHyps:    MeTTa list of (Typecode Var) — append order
;;;   FLabels:  opaque Prolog assoc (Var → Label)
;;;   EHyps:    MeTTa list of ($label $stmt) pairs — append order
;;;
;;; Label entries stored in Labels assoc:
;;;   (hyp f (Typecode Var))           — floating hypothesis
;;;   (hyp e Statement)                — essential hypothesis
;;;   (assertion DVs FHyps EHyps Stmt) — axiom or theorem

(= (empty-frame)
   (frame (ds_empty_ordset) (ds_empty_ordset) () (ds_empty_assoc) ()))

(= (initial-state)
   (state (ds_empty_ordset) ((empty-frame)) (ds_empty_assoc)))

(= (push-frame (state $c $fs $l))
   (state $c (cons-atom (empty-frame) $fs) $l))

(= (pop-frame (state $c $fs $l))
   (let ($top $rest) (decons-atom $fs)
     (state $c $rest $l)))

;;; lookup-v-fs: is token an active variable in any frame?
(= (lookup-v-fs $tok $fs)
   (if (== (size-atom $fs) 0)
       False
       (let ($f $rest) (decons-atom $fs)
         (let (frame $vars $d $fh $fl $eh) $f
           (if (ds_ord_member $tok $vars)
               True
               (lookup-v-fs $tok $rest))))))

;;; lookup-f-fs: find f-hyp label for variable in frame stack
(= (lookup-f-fs $var $fs)
   (if (== (size-atom $fs) 0)
       not_found
       (let ($f $rest) (decons-atom $fs)
         (let (frame $v $d $fh $fl $eh) $f
           (let $label (ds_assoc_get $var $fl)
             (if (== $label not_found)
                 (lookup-f-fs $var $rest)
                 $label))))))

;;; lookup-d-fs: is DV pair declared in any frame?
(= (lookup-d-fs $x $y $fs)
   (let $key (ds_dv_key $x $y)
     (lookup-d-key $key $fs)))

(= (lookup-d-key $key $fs)
   (if (== (size-atom $fs) 0)
       False
       (let ($f $rest) (decons-atom $fs)
         (let (frame $v $dvs $fh $fl $eh) $f
           (if (ds_ord_member $key $dvs)
               True
               (lookup-d-key $key $rest))))))

;;; ========== Section 3: Statement Handlers ==========

;;; is-error: check if value is an error
;;; Uses case for safe structural matching — no car-atom/size-atom
;;; which would trigger evaluation of opaque Prolog terms
(= (is-error $x)
   (case $x
     (((Error $a $b) True)
      ($_ False))))

;;; append-to-list: append element to end of MeTTa expression
(= (append-to-list $list $elem)
   (if (== (size-atom $list) 0)
       ($elem)
       (let ($h $t) (decons-atom $list)
         (cons-atom $h (append-to-list $t $elem)))))

;;; concat-lists: concatenate two MeTTa expressions
(= (concat-lists $a $b)
   (if (== (size-atom $a) 0)
       $b
       (let ($h $t) (decons-atom $a)
         (cons-atom $h (concat-lists $t $b)))))

;;; add-c: add constant
(= (add-c $tok (state $c $fs $l))
   (state (ds_ord_add $tok $c) $fs $l))

;;; foldl-add-c: fold add-c over symbol list
(= (foldl-add-c $syms $state)
   (if (== (size-atom $syms) 0)
       $state
       (let ($h $t) (decons-atom $syms)
         (foldl-add-c $t (add-c $h $state)))))

;;; add-v: add variable to current frame
(= (add-v $tok (state $c $fs $l))
   (let ($f $rest) (decons-atom $fs)
     (let (frame $vars $dvs $fh $fl $eh) $f
       (state $c
         (cons-atom (frame (ds_ord_add $tok $vars) $dvs $fh $fl $eh) $rest)
         $l))))

;;; foldl-add-v: fold add-v over var list
(= (foldl-add-v $vars $state)
   (if (== (size-atom $vars) 0)
       $state
       (let ($h $t) (decons-atom $vars)
         (foldl-add-v $t (add-v $h $state)))))

;;; add-f: add floating hypothesis
;;; FHyps stores ($tc $var) pairs as MeTTa expressions (for make-assertion)
;;; Label entry stores (hyp f stmt) where stmt is opaque Prolog list [tc, var]
(= (add-f $label $tc $var (state $c $fs $l))
   (let ($f $rest) (decons-atom $fs)
     (let (frame $vars $dvs $fh $fl $eh) $f
       (let $fh1 (append-to-list $fh ($tc $var))
         (let $fl1 (ds_assoc_put $var $label $fl)
           (let $fstmt (ds_stmt_cons $tc (ds_stmt_cons $var (ds_stmt_empty)))
             (let $l1 (ds_assoc_put $label (hyp f $fstmt) $l)
               (state $c
                 (cons-atom (frame $vars $dvs $fh1 $fl1 $eh) $rest)
                 $l1))))))))

;;; add-e: add essential hypothesis
;;; EHyps stores (ep $label $stmt) triples — tagged to prevent PeTTa evaluation
;;; (e.g. label "min" would be evaluated as built-in min function without tagging)
(= (add-e $label $stmt (state $c $fs $l))
   (let ($f $rest) (decons-atom $fs)
     (let (frame $vars $dvs $fh $fl $eh) $f
       (let $eh1 (append-to-list $eh (ep $label $stmt))
         (let $l1 (ds_assoc_put $label (hyp e $stmt) $l)
           (state $c
             (cons-atom (frame $vars $dvs $fh $fl $eh1) $rest)
             $l1))))))

;;; add-d: add disjoint variable pairs
(= (add-d $varlist (state $c $fs $l))
   (let $new_pairs (ds_make_dv_pairs $varlist)
     (let ($f $rest) (decons-atom $fs)
       (let (frame $vars $dvs $fh $fl $eh) $f
         (let $dvs1 (ds_ord_union $dvs $new_pairs)
           (state $c
             (cons-atom (frame $vars $dvs1 $fh $fl $eh) $rest)
             $l))))))

;;; ========== Section 4: make-assertion ==========

;;; collect-all-ehyps: gather all e-hyps from all frames, bottom-up
;;; Returns list of ($label $stmt) pairs
(= (collect-all-ehyps $fs)
   (let $reversed (ds_reverse $fs)
     (collect-ehyps-acc $reversed ())))

(= (collect-ehyps-acc $fs $acc)
   (if (== (size-atom $fs) 0)
       $acc
       (let ($f $rest) (decons-atom $fs)
         (let (frame $v $d $fh $fl $eh) $f
           (collect-ehyps-acc $rest (concat-lists $acc $eh))))))

;;; collect-all-fhyps: gather all f-hyps from all frames, bottom-up
(= (collect-all-fhyps $fs)
   (let $reversed (ds_reverse $fs)
     (collect-fhyps-acc $reversed ())))

(= (collect-fhyps-acc $fs $acc)
   (if (== (size-atom $fs) 0)
       $acc
       (let ($f $rest) (decons-atom $fs)
         (let (frame $v $d $fh $fl $eh) $f
           (collect-fhyps-acc $rest (concat-lists $acc $fh))))))

;;; get-ehyp-stmts-from-pairs: extract just statements from ehyp (ep label stmt) triples
(= (get-ehyp-stmts-from-pairs $ehyps)
   (if (== (size-atom $ehyps) 0)
       ()
       (let ($triple $rest) (decons-atom $ehyps)
         (let (ep $label $stmt) $triple
           (cons-atom $stmt (get-ehyp-stmts-from-pairs $rest))))))

;;; get-ehyp-labels-from-pairs: extract just labels from ehyp (ep label stmt) triples
(= (get-ehyp-labels-from-pairs $ehyps)
   (if (== (size-atom $ehyps) 0)
       ()
       (let ($triple $rest) (decons-atom $ehyps)
         (let (ep $label $stmt) $triple
           (cons-atom $label (get-ehyp-labels-from-pairs $rest))))))

;;; find-vars-in-expr: find all active variables in a statement expression
(= (find-vars-in-expr $stmt $fs)
   (find-vars-acc $stmt $fs (ds_empty_ordset)))

(= (find-vars-acc $stmt $fs $acc)
   (if (== (ds_stmt_size $stmt) 0)
       $acc
       (let $tok (ds_stmt_head $stmt)
         (let $rest (ds_stmt_tail $stmt)
           (if (lookup-v-fs $tok $fs)
               (find-vars-acc $rest $fs (ds_ord_add $tok $acc))
               (find-vars-acc $rest $fs $acc))))))

;;; find-vars-in-stmts: find vars across multiple statements
(= (find-vars-in-stmts $stmts $fs $acc)
   (if (== (size-atom $stmts) 0)
       $acc
       (let ($stmt $rest) (decons-atom $stmts)
         (let $vars (find-vars-in-expr $stmt $fs)
           (find-vars-in-stmts $rest $fs (ds_ord_union $acc $vars))))))

;;; filter-fhyps-by-vars: keep only fhyps whose var is in mand_vars
(= (filter-fhyps-by-vars $fhyps $mand_vars)
   (if (== (size-atom $fhyps) 0)
       ()
       (let ($pair $rest) (decons-atom $fhyps)
         (let ($tc $var) $pair
           (if (ds_ord_member $var $mand_vars)
               (cons-atom $pair (filter-fhyps-by-vars $rest $mand_vars))
               (filter-fhyps-by-vars $rest $mand_vars))))))

;;; collect-all-dvs: gather all DV pairs from all frames, restricted to mandatory vars
(= (collect-all-dvs $fs $mand_vars)
   (collect-dvs-acc $fs $mand_vars (ds_empty_ordset)))

(= (collect-dvs-acc $fs $mv $acc)
   (if (== (size-atom $fs) 0)
       $acc
       (let ($f $rest) (decons-atom $fs)
         (let (frame $v $dvs $fh $fl $eh) $f
           (let $filtered (ds_filter_dvs_mandvars $dvs $mv)
             (collect-dvs-acc $rest $mv (ds_ord_union $acc $filtered)))))))

;;; make-assertion: build assertion from conclusion statement
;;; Returns (assertion DVs FHyps EHyps Conclusion)
;;; EHyps here are (ep $label $stmt) triples
(= (make-assertion $stmt $fs)
   (let $all_ehyps (collect-all-ehyps $fs)
     (let $all_fhyps (collect-all-fhyps $fs)
       ;; Find mandatory vars: vars in ehyps + conclusion
       (let $ehyp_stmts (get-ehyp-stmts-from-pairs $all_ehyps)
         (let $ehyp_vars (find-vars-in-stmts $ehyp_stmts $fs (ds_empty_ordset))
           (let $stmt_vars (find-vars-in-expr $stmt $fs)
             (let $mand_vars (ds_ord_union $ehyp_vars $stmt_vars)
               ;; Filter fhyps to mandatory ones and add their vars
               (let $mand_fhyps (filter-fhyps-by-vars $all_fhyps $mand_vars)
                 (let $fhyp_vars (fhyps-to-varset $mand_fhyps)
                   (let $all_mand (ds_ord_union $mand_vars $fhyp_vars)
                     ;; Collect DVs restricted to all mandatory vars
                     (let $dvs (collect-all-dvs $fs $all_mand)
                       (assertion $dvs $mand_fhyps $all_ehyps $stmt))))))))))))


;;; fhyps-to-varset: extract var ordset from fhyps list
(= (fhyps-to-varset $fhyps)
   (fhyps-to-varset-acc $fhyps (ds_empty_ordset)))

(= (fhyps-to-varset-acc $fhyps $acc)
   (if (== (size-atom $fhyps) 0)
       $acc
       (let ($pair $rest) (decons-atom $fhyps)
         (let ($tc $var) $pair
           (fhyps-to-varset-acc $rest (ds_ord_add $var $acc))))))

;;; ========== Section 5: Substitution + DV Checking ==========

;;; build-subst: build substitution assoc from fhyps and stack entries
;;; Returns (ok $subst) or (Error ...) — tagged to avoid inspecting opaque assoc
(= (build-subst $fhyps $entries)
   (build-subst-acc $fhyps $entries (ds_empty_assoc)))

(= (build-subst-acc $fhyps $entries $subst)
   (if (== (size-atom $fhyps) 0)
       (ok $subst)
       (let ($fh $frest) (decons-atom $fhyps)
         (let ($entry $erest) (decons-atom $entries)
           (let ($tc $var) $fh
             ;; Entry is an opaque Prolog statement list like [wff, ph, ->, ps]
             ;; First token must match typecode
             (let $entry_tc (ds_stmt_head $entry)
               (let $entry_math (ds_stmt_tail $entry)
                 (if (!= $entry_tc $tc)
                     (Error (typecode_mismatch $tc $entry_tc $var) "Typecode mismatch")
                     (build-subst-acc $frest $erest
                       (ds_assoc_put $var $entry_math $subst))))))))))

;;; apply-subst: apply substitution to statement (opaque Prolog list)
(= (apply-subst $stmt $subst)
   (if (== (ds_stmt_size $stmt) 0)
       (ds_stmt_empty)
       (let $tok (ds_stmt_head $stmt)
         (let $rest (ds_stmt_tail $stmt)
           (let $repl (ds_assoc_get $tok $subst)
             (if (== $repl not_found)
                 (ds_stmt_cons $tok (apply-subst $rest $subst))
                 (ds_stmt_concat $repl (apply-subst $rest $subst))))))))

;;; check-ehyps: verify essential hypotheses match
;;; $ehyps and $entries are MeTTa lists of opaque Prolog statement lists
(= (check-ehyps $ehyps $entries $subst)
   (if (== (size-atom $ehyps) 0)
       True
       (let ($eh $erest) (decons-atom $ehyps)
         (let ($entry $entrest) (decons-atom $entries)
           (let $expected (apply-subst $eh $subst)
             (if (ds_stmt_eq $entry $expected)
                 (check-ehyps $erest $entrest $subst)
                 (Error (ehyp_mismatch $entry $expected) "E-hyp mismatch")))))))

;;; check-dvs: verify disjoint variable constraints
(= (check-dvs $dvs $subst $fs)
   (if (== (size-atom $dvs) 0)
       True
       (let ($pair $rest) (decons-atom $dvs)
         (let $x (ds_pair_fst $pair)
           (let $y (ds_pair_snd $pair)
             (let $sx (ds_assoc_get $x $subst)
               (let $sy (ds_assoc_get $y $subst)
                 (if (== $sx not_found)
                     (check-dvs $rest $subst $fs)
                     (if (== $sy not_found)
                         (check-dvs $rest $subst $fs)
                         (let $vx (find-vars-in-expr $sx $fs)
                           (let $vy (find-vars-in-expr $sy $fs)
                             (let $result (check-dv-cross $vx $vy $fs)
                               (if (is-error $result)
                                   $result
                                   (check-dvs $rest $subst $fs))))))))))))))

;;; check-dv-cross: for all x in VX, y in VY, check DV(x,y)
(= (check-dv-cross $vx $vy $fs)
   (if (== (size-atom $vx) 0)
       True
       (let ($x0 $xrest) (decons-atom $vx)
         (let $r (check-dv-one-against-all $x0 $vy $fs)
           (if (is-error $r) $r
               (check-dv-cross $xrest $vy $fs))))))

(= (check-dv-one-against-all $x0 $vy $fs)
   (if (== (size-atom $vy) 0)
       True
       (let ($y0 $yrest) (decons-atom $vy)
         (if (== $x0 $y0)
             (Error ($x0 $y0) "DV violation: same variable")
             (if (== (lookup-d-fs $x0 $y0 $fs) False)
                 (Error ($x0 $y0) "DV violation: not declared")
                 (check-dv-one-against-all $x0 $yrest $fs))))))

;;; ========== Section 6: RPN Stack Machine ==========

;;; split-stack: pop N elements from stack
;;; Returns (popped-in-order remaining-stack)
(= (split-stack $stack $n)
   (split-stack-acc $stack $n ()))

(= (split-stack-acc $stack $n $acc)
   (if (== $n 0)
       ($acc $stack)
       (let ($top $rest) (decons-atom $stack)
         (split-stack-acc $rest (- $n 1) (append-to-list $acc $top)))))

;;; split-at: split list at position N, returns (first second)
(= (split-at $list $n)
   (split-at-acc $list $n ()))

(= (split-at-acc $list $n $acc)
   (if (== $n 0)
       ((reverse-list $acc) $list)
       (let ($h $t) (decons-atom $list)
         (split-at-acc $t (- $n 1) (cons-atom $h $acc)))))

;;; reverse-list
(= (reverse-list $list)
   (reverse-acc $list ()))

(= (reverse-acc $list $acc)
   (if (== (size-atom $list) 0)
       $acc
       (let ($h $t) (decons-atom $list)
         (reverse-acc $t (cons-atom $h $acc)))))

;;; treat-step: process one proof step
;;; Entry types:
;;;   (hyp f (tc var))       — floating hypothesis: push (tc var) onto stack
;;;   (hyp e stmt)           — essential hypothesis: push stmt onto stack
;;;   (assertion dvs fh eh c) — assertion: verify and push substituted conclusion
(= (treat-step $entry $stack $state)
   (let $type (car-atom $entry)
     (if (== $type hyp)
         ;; Hypothesis: push data onto stack (index 2 = the statement/pair)
         (cons-atom (index-atom $entry 2) $stack)
         ;; Assertion: pop hyps, build subst, check, push conclusion
         (let (assertion $dvs $fhyps $ehyps $conclusion) $entry
           (treat-assertion-body $dvs $fhyps (get-ehyp-stmts-from-pairs $ehyps) $conclusion $stack $state)))))

;;; treat-assertion-body: the core of assertion verification
(= (treat-assertion-body $dvs $fhyps $ehyp_stmts $conclusion $stack $state)
   (let (state $c $fs $l) $state
     (let $nf (size-atom $fhyps)
       (let $ne (size-atom $ehyp_stmts)
         (let $npop (+ $nf $ne)
           (let $slen (size-atom $stack)
             (if (< $slen $npop)
                 (Error (stack_underflow $npop $slen) "Stack underflow")
                 ;; Pop entries from stack (LIFO order), reverse to get push-order
                 (let ($popped_rev $kept) (split-stack $stack $npop)
                   (let $popped (reverse-list $popped_rev)
                     (let ($f_entries $e_entries) (split-at $popped $nf)
                       ;; Build substitution from fhyps + their stack entries
                       (let $bsr (build-subst $fhyps $f_entries)
                         (if (is-error $bsr) $bsr
                         (let (ok $subst) $bsr
                             ;; Check essential hypotheses
                             (let $eh_check (check-ehyps $ehyp_stmts $e_entries $subst)
                               (if (is-error $eh_check) $eh_check
                                   ;; Check DV constraints
                                   (let $dv_check (check-dvs $dvs $subst $fs)
                                     (if (is-error $dv_check) $dv_check
                                         ;; Apply substitution to conclusion and push
                                         (let $result (apply-subst $conclusion $subst)
                                           (cons-atom $result $kept)))))))))))))))))))

;;; ========== Section 7: Normal Proof Processing ==========

(= (treat-normal-proof $labels $state)
   (treat-normal-acc $labels $state ()))

(= (treat-normal-acc $labels $state $stack)
   (if (== (size-atom $labels) 0)
       $stack
       (let ($label $rest) (decons-atom $labels)
         ;; Handle ? (incomplete step)
         (if (or (== $label ?) (== $label "?"))
             (incomplete)
             (let (state $c $fs $l) $state
               (let $info (ds_assoc_get $label $l)
                 (if (== $info not_found)
                     (Error (unknown_label $label) "Unknown label in proof")
                     (let $stack1 (treat-step $info $stack $state)
                       (if (is-error $stack1)
                           $stack1
                           (treat-normal-acc $rest $state $stack1))))))))))

;;; ========== Section 8: Compressed Proof ==========

;;; get-mand-fhyp-labels: get f-hyp labels for mandatory variables
(= (get-mand-fhyp-labels $fhyps $needed_vars $fs)
   (if (== (size-atom $fhyps) 0)
       ()
       (let ($pair $rest) (decons-atom $fhyps)
         (let ($tc $var) $pair
           (if (ds_ord_member $var $needed_vars)
               (let $label (lookup-f-fs $var $fs)
                 (cons-atom $label (get-mand-fhyp-labels $rest $needed_vars $fs)))
               (get-mand-fhyp-labels $rest $needed_vars $fs))))))

;;; treat-compressed-proof
(= (treat-compressed-proof $plabels $psteps $conclusion $state)
   (let (state $c $fs $l) $state
     (let $all_fhyps (collect-all-fhyps $fs)
       (let $all_ehyps (collect-all-ehyps $fs)
         (let $ehyp_stmts (get-ehyp-stmts-from-pairs $all_ehyps)
           (let $ehyp_vars (find-vars-in-stmts $ehyp_stmts $fs (ds_empty_ordset))
             (let $stmt_vars (find-vars-in-expr $conclusion $fs)
               (let $needed_vars (ds_ord_union $ehyp_vars $stmt_vars)
                 (let $fhyp_labels (get-mand-fhyp-labels $all_fhyps $needed_vars $fs)
                   (let $ehyp_labels (get-ehyp-labels-from-pairs $all_ehyps)
                     (let $mand_hyps (concat-lists $fhyp_labels $ehyp_labels)
                       (let $num_mand (size-atom $mand_hyps)
                         (let $num_labels (ds_length $plabels)
                           (process-compressed-steps $psteps $mand_hyps $plabels
                                                     $num_mand $num_labels
                                                     $state () ()))))))))))))))

;;; process-compressed-steps
(= (process-compressed-steps $steps $mand $plabels $nm $nl $state $stack $saved)
   (if (== (ds_length $steps) 0)
       $stack
       (let $idx (ds_stmt_head $steps)
         (let $rest (ds_stmt_tail $steps)
         ;; Check for save marker
         (if (or (== $idx -1) (== $idx save))
             (if (== (size-atom $stack) 0)
                 (Error (Z-save) "Cannot save: empty stack")
                 (let ($top $_) (decons-atom $stack)
                   (process-compressed-steps $rest $mand $plabels $nm $nl
                     $state $stack (append-to-list $saved $top))))
             ;; Check for incomplete marker
             (if (== (get-metatype $idx) Symbol)
                 (if (or (== $idx ?) (== $idx incomplete))
                     (incomplete)
                     (Error (unknown_symbol $idx) "Unknown symbol in compressed proof"))
                 ;; Numeric index
                 (let $num_total (+ $nm $nl)
                   (if (< $idx $nm)
                       ;; Index into mandatory hyps
                       (let $label (index-atom $mand $idx)
                         (dispatch-compressed-label $label $rest $mand $plabels $nm $nl $state $stack $saved))
                       (if (< $idx $num_total)
                           ;; Index into explicit labels
                           (let $label_idx (- $idx $nm)
                             (let $label (ds_nth0 $label_idx $plabels)
                               (dispatch-compressed-label $label $rest $mand $plabels $nm $nl $state $stack $saved)))
                           ;; Reference to saved statement
                           (let $save_idx (- $idx $num_total)
                             (if (>= $save_idx (size-atom $saved))
                                 (Error (save_idx_oob $save_idx (size-atom $saved)) "Save index out of bounds")
                                 (let $saved_stmt (index-atom $saved $save_idx)
                                   (process-compressed-steps $rest $mand $plabels $nm $nl
                                     $state (cons-atom $saved_stmt $stack) $saved)))))))))))))

;;; dispatch-compressed-label
(= (dispatch-compressed-label $label $rest $mand $plabels $nm $nl $state $stack $saved)
   (let (state $c $fs $l) $state
     (let $info (ds_assoc_get $label $l)
       (if (== $info not_found)
           (Error (unknown_label $label) "Unknown label in compressed proof")
           (let $stack1 (treat-step $info $stack $state)
             (if (is-error $stack1)
                 $stack1
                 (process-compressed-steps $rest $mand $plabels $nm $nl
                   $state $stack1 $saved)))))))

;;; ========== Section 9: Verify + Statement Dispatch ==========

;;; verify-proof: verify proof yields expected conclusion
(= (verify-proof $fhyps $ehyp_stmts $conclusion $proof $state)
   (let $stack_result (verify-dispatch $proof $conclusion $state)
     (if (is-error $stack_result) $stack_result
       (if (== $stack_result (incomplete)) (incomplete)
           (if (== (size-atom $stack_result) 0)
               (Error empty_stack "Empty stack at end of proof")
               (if (> (size-atom $stack_result) 1)
                   (Error (multiple_entries (size-atom $stack_result)) "Stack has more than one entry")
                   (let ($top) $stack_result
                     (if (ds_stmt_eq $top $conclusion)
                         ok
                         (Error (conclusion_mismatch $top $conclusion) "Stack doesn't match conclusion")))))))))

;;; verify-dispatch: route to normal or compressed
;;; $proof is either a MeTTa list (normal) or Prolog compound (compressed/compressed_dag)
(= (verify-dispatch $proof $conclusion $state)
   (let $pfunctor (ds_stmt_functor $proof)
     (case $pfunctor
       ((compressed
           (let $labels (ds_stmt_arg $proof 1)
             (let $steps (ds_stmt_arg $proof 2)
               (treat-compressed-proof $labels $steps $conclusion $state))))
        (compressed_dag
           (let $labels (ds_stmt_arg $proof 1)
             (let $steps (ds_stmt_arg $proof 2)
               (treat-compressed-proof $labels $steps $conclusion $state))))
        ($_ (treat-normal-proof $proof $state))))))

;;; process-statement: dispatch on compound type
(= (process-statement $stmt $state)
   (let $type (ds_stmt_functor $stmt)
     (case $type
       ((c (let $syms (ds_stmt_arg $stmt 1)
             (foldl-add-c $syms $state)))
        (v (let $vars (ds_stmt_arg $stmt 1)
             (foldl-add-v $vars $state)))
        (f (let $label (ds_stmt_arg $stmt 1)
             (let $tc (ds_stmt_arg $stmt 2)
               (let $var (ds_stmt_arg $stmt 3)
                 (add-f $label $tc $var $state)))))
        (e (let $label (ds_stmt_arg $stmt 1)
             (let $tc (ds_stmt_arg $stmt 2)
               (let $math (ds_stmt_arg $stmt 3)
                 (add-e $label (ds_stmt_from_args $tc $math) $state)))))
        (d (let $vars (ds_stmt_arg $stmt 1)
             (add-d $vars $state)))
        (a (let $label (ds_stmt_arg $stmt 1)
             (let $tc (ds_stmt_arg $stmt 2)
               (let $math (ds_stmt_arg $stmt 3)
                 (let $conclusion (ds_stmt_from_args $tc $math)
                   (let (state $c $fs $l) $state
                     (let $asrt (make-assertion $conclusion $fs)
                       (let $l1 (ds_assoc_put $label $asrt $l)
                         (state $c $fs $l1)))))))))
        (p (process-p-stmt $stmt $state))
        (open_frame (push-frame $state))
        (close_frame (pop-frame $state))))))

;;; process-p-stmt: handle $p theorem — extracted to reduce nesting depth
(= (process-p-stmt $stmt $state)
   (let $label (ds_stmt_arg $stmt 1)
     (let $tc (ds_stmt_arg $stmt 2)
       (let $math (ds_stmt_arg $stmt 3)
         (let $proof (ds_stmt_arg $stmt 4)
           (let $conclusion (ds_stmt_from_args $tc $math)
             (process-p-verify $label $conclusion $proof $state)))))))

(= (process-p-verify $label $conclusion $proof $state)
   (let (state $c $fs $l) $state
     (let $asrt (make-assertion $conclusion $fs)
       (let (assertion $dvs $fhyps $ehyps $concl) $asrt
         (let $ehyp_stmts (get-ehyp-stmts-from-pairs $ehyps)
           (let $vresult (verify-proof $fhyps $ehyp_stmts $conclusion $proof $state)
             (process-p-handle-result $label $asrt $state $vresult)))))))

(= (process-p-handle-result $label $asrt $state $vresult)
   (let (state $c $fs $l) $state
     (case $vresult
       ((ok (let $l1 (ds_assoc_put $label $asrt $l)
                (state $c $fs $l1)))
        ((incomplete)
            (let $l1 (ds_assoc_put $label $asrt $l)
                (state $c $fs $l1)))
        ($other
            (let $_ (println! "")
              (let $_ (println! ("PROOF FAILED:" $label $other))
                $other)))))))

;;; process-all-statements: fold process-statement over all parsed statements
(= (process-all-statements $stmts $state)
   (if (== (size-atom $stmts) 0)
       $state
       (let ($stmt $rest) (decons-atom $stmts)
         (let $state1 (process-statement $stmt $state)
           (if (is-error $state1)
               $state1
               (process-all-statements $rest $state1))))))

;;; ========== Section 10: Main / CLI ==========

(= (get-first-non-flag-arg $idx)
   (let $arg (get_cmdline_arg $idx)
     (if (== $arg Empty)
         Empty
         (let $is_flag (collapse (is_flag_arg $arg))
           (if (== (car-atom $is_flag) true)
               (get-first-non-flag-arg (+ $idx 1))
               $arg)))))

!(let $cmdline_arg (get-first-non-flag-arg 0)
   (let $input_file (if (== $cmdline_arg Empty)
                        (get_env_var_or_default "MM_INPUT_FILE" "../metamath/metamath-test/tests/core/small/demo0.mm")
                        $cmdline_arg)
     (let $stmts (ds_parse_mm $input_file)
       (let $n (ds_length $stmts)
         (progn
           (println! ("Parsed" $n "statements. Verifying..."))
           (let $result (process-all-statements $stmts (initial-state))
             (if (is-error $result)
                     (progn
                       (println! "")
                       (println! "=== VERIFICATION FAILED ===")
                       (halt_with_code 1))
                     (progn
                       (println! "")
                       (println! "=== Verification Complete ===")))))))))
