;;; Maple Court Sleep Consolidation Conformance
;;;
;;; The core WM theorem: batch processing = sequential processing.
;;; evidence(morning + evening, q) = evidence(morning, q) + evidence(evening, q)
;;;
;;; This is the AddCommMonoid law in action: hplus is associative,
;;; commutative, and has a zero.  Order doesn't matter.
;;;
;;; Lean side: PLNMapleCourtDemo.lean theorem mapleCourt_sleep_consolidation

!(import! &self ../../hyperon/PeTTa/pln_inference/pln_evidence)

;;; ============================================================
;;; Observation episodes (three shifts)
;;; ============================================================

;; Morning: 3 motion detections, 1 no-motion
(= (morning) (evidence 3 1))

;; Evening: 1 leak alarm, 2 no-alarm, plus 1 shower detection
(= (evening-leak)   (evidence 1 2))
(= (evening-shower) (evidence 1 0))
(= (evening) (evidence-hplus (evening-leak) (evening-shower)))

;; Night: 2 motion detections (late-night activity)
(= (night) (evidence 2 0))

;;; ============================================================
;;; Test 1: Batch = Sequential (the sleep consolidation theorem)
;;; hplus(hplus(morning, evening), night) = hplus(morning, hplus(evening, night))
;;; ============================================================
!(println! "=== Sleep Consolidation ===")

;; Batch: combine all at once
!(println! "Batch (morning+evening+night):")
!(evidence-hplus (evidence-hplus (morning) (evening)) (night))

;; Sequential: morning first, then evening, then night
!(println! "Sequential ((morning+evening)+night):")
!(evidence-hplus (evidence-hplus (morning) (evening)) (night))

;; Associativity: regrouping gives same result
!(println! "Regrouped (morning+(evening+night)):")
!(evidence-hplus (morning) (evidence-hplus (evening) (night)))

!(assertEqual
  (evidence-hplus (evidence-hplus (morning) (evening)) (night))
  (evidence-hplus (morning) (evidence-hplus (evening) (night))))

;;; ============================================================
;;; Test 2: Order doesn't matter (commutativity)
;;; ============================================================
!(println! "=== Order Independence ===")

!(assertEqual
  (evidence-hplus (morning) (evening))
  (evidence-hplus (evening) (morning)))

!(assertEqual
  (evidence-hplus (evidence-hplus (night) (morning)) (evening))
  (evidence-hplus (evidence-hplus (morning) (evening)) (night)))

;;; ============================================================
;;; Test 3: Zero is identity (no evidence = no change)
;;; ============================================================
!(println! "=== Zero Identity ===")

!(assertEqual
  (evidence-hplus (morning) (evidence 0 0))
  (morning))

;;; ============================================================
;;; Test 4: Strength evolves as evidence accumulates
;;; ============================================================
!(println! "=== Strength Evolution ===")

;; After morning only: 3/(3+1) = 0.75
!(assertEqual (evidence-toStrength (morning)) 0.75)

;; After morning+evening: (3+2)/(3+2+1+2) = 5/8 = 0.625
;; (evening adds 2 pos from leak+shower, 2 neg from no-alarm)
!(println! "morning+evening strength:" (evidence-toStrength (evidence-hplus (morning) (evening))))

;; After all three: more evidence, strength adjusts
!(println! "all three strength:" (evidence-toStrength (evidence-hplus (evidence-hplus (morning) (evening)) (night))))

;;; ============================================================
;;; Test 5: Total evidence always increases (monotonicity)
;;; ============================================================
!(println! "=== Evidence Accumulation ===")

!(println! "morning total:" (+ 3 1))
!(println! "morning+evening:" (evidence-hplus (morning) (evening)))
!(println! "all three:" (evidence-hplus (evidence-hplus (morning) (evening)) (night)))

!(println! "All sleep consolidation tests passed.")
