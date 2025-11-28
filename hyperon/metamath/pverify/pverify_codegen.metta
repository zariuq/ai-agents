;;; pverify_codegen.metta - Generate demo0_petta-style code from parsed Metamath
;;; Uses Prolog parser, outputs MeTTa code (doesn't execute verification)

!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_he)
!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_prolog)

!(import_prolog_functions_from_file "/home/zar/claude/hyperon/metamath/pverify/mm_primitives.pl"
  (parse_mm_file))

;;; ==========================================================================
;;; Code Generation Functions - Just println the code directly
;;; ==========================================================================

(= (tuple-prepend $elem $tuple)
   (cons-atom $elem $tuple))

;; Generate code for each statement type
(= (gen-statement $stmt)
   (let ($tag $data) (decons-atom $stmt)
     (gen-by-tag $tag $data)))

(= (gen-by-tag c $rest)
   (let ($symbols $_) (decons-atom $rest)
     (gen-c-symbols $symbols)))

(= (gen-by-tag v $rest)
   (let ($vars $_) (decons-atom $rest)
     (gen-v-symbols $vars)))

(= (gen-by-tag f $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($var $_) (decons-atom $rest3)
         (println! (!(add_f &kb $label $type $var 1)))))))

(= (gen-by-tag e $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $_) (decons-atom $rest3)
         (println! (!(add_e &kb $label (tuple-prepend $type $math) 2)))))))

(= (gen-by-tag a $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $_) (decons-atom $rest3)
         (println! (!(add_a &kb $label (tuple-prepend $type $math))))))))

(= (gen-by-tag p $rest)
   (let ($label $rest2) (decons-atom $rest)
     (let ($type $rest3) (decons-atom $rest2)
       (let ($math $rest4) (decons-atom $rest3)
         (let ($proof $_) (decons-atom $rest4)
           (println! (!(add_p &kb &stack &sp $label (tuple-prepend $type $math) $proof True))))))))

(= (gen-by-tag d $rest)
   (let ($vars $_) (decons-atom $rest)
     (println! (!(add_d &kb $vars &fd)))))

(= (gen-by-tag open_frame $_)
   (println! (!(push-frame &fd))))

(= (gen-by-tag close_frame $_)
   (println! (!(pop-frame &kb &fd))))

;; Process symbols (c and v statements)
(= (gen-c-symbols $symbols)
   (if (== (size-atom $symbols) 0)
       Empty
       (let ($first $rest) (decons-atom $symbols)
         (let $_ (println! (!(add_c &kb $first)))
           (gen-c-symbols $rest)))))

(= (gen-v-symbols $vars)
   (if (== (size-atom $vars) 0)
       Empty
       (let ($first $rest) (decons-atom $vars)
         (let $_ (println! (!(add_v &kb $first 1)))
           (gen-v-symbols $rest)))))

;; Generate all statements
(= (gen-statements $stmts)
   (map-atom $stmts $stmt (gen-statement $stmt)))

;;; ==========================================================================
;;; Main
;;; ==========================================================================

!(println! (!(bind! &sp (new-state 0))))
!(println! (!(bind! &fd (new-state 0))))
!(println! (!(import! &self /home/zar/claude/hyperon/PeTTa/lib/lib_he)))
!(println! (!(import! &self /home/zar/claude/hyperon/metamath/mmverify/mmverify-utils_petta)))
!(println! (!(push-frame &fd)))

!(let $stmts (parse_mm_file "/home/zar/claude/hyperon/metamath/mmverify/tests/demo0.mm")
  (gen-statements $stmts))

!(println! (!(pop-frame &kb &fd)))
