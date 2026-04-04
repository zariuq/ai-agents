;;; Maple Court BN Motifs Conformance
;;;
;;; Tests the three canonical BN structures from Maple Court:
;;;   Collider: ShowerRunning → BathroomHumidity ← PipeLeak
;;;   Fork:     RoomOccupied → MotionDetected, RoomOccupied → PowerUseHigh
;;;   Chain:    PipeLeak → WallHumidity → MoldRisk
;;;
;;; Lean side: PLNMapleCourtDemo.lean (34 theorems, 0 sorry)

!(import! &self ../../hyperon/PeTTa/pln_inference/pln_evidence)
!(import! &self ../../hyperon/PeTTa/lib/lib_pln)

;;; ============================================================
;;; Evidence for each node (binary: pos/neg observation counts)
;;; ============================================================

;; Collider parents
(= (shower-evidence) (evidence 2 1))   ; 2 shower-on, 1 shower-off
(= (leak-evidence)   (evidence 1 4))   ; 1 leak alarm, 4 no-alarm

;; Fork: occupancy evidence from two sensors
(= (motion-evidence) (evidence 3 0))   ; 3 motion detections, 0 misses
(= (power-evidence)  (evidence 2 1))   ; 2 high-power, 1 low-power

;; Chain: link evidence
(= (leak-to-wall)    (evidence 4 1))   ; P(wall humid | leak) strong
(= (wall-to-mold)    (evidence 3 2))   ; P(mold | wall humid) moderate

;;; ============================================================
;;; Test 1: Collider — independent sources combine additively
;;; When we haven't conditioned on humidity, shower and leak
;;; are independent.  Their evidence combines via hplus.
;;; ============================================================
!(println! "=== Collider Tests ===")

!(assertEqual
  (evidence-hplus (shower-evidence) (leak-evidence))
  (evidence 3 5))

;; Combined strength: 3/(3+5) = 0.375
!(assertEqual
  (evidence-toStrength (evidence-hplus (shower-evidence) (leak-evidence)))
  0.375)

;;; ============================================================
;;; Test 2: Fork — common source, evidence from two channels
;;; Both motion and power evidence bear on occupancy.
;;; ============================================================
!(println! "=== Fork Tests ===")

;; Combining motion + power evidence for occupancy
!(assertEqual
  (evidence-hplus (motion-evidence) (power-evidence))
  (evidence 5 1))

;; Strong occupancy evidence: 5/(5+1) ≈ 0.833
!(assertEqual
  (evidence-toStrength (evidence 5 1))
  (/ 5 6))

;;; ============================================================
;;; Test 3: Chain — deduction through intermediate node
;;; PipeLeak → WallHumidity → MoldRisk
;;; The tensor (evidence product) gives the direct-path lower
;;; bound for the chain.
;;; ============================================================
!(println! "=== Chain Tests ===")

;; Tensor: direct path bound
!(assertEqual
  (evidence-tensor (leak-to-wall) (wall-to-mold))
  (evidence 12 2))

;; Tensor strength: 12/(12+2) ≈ 0.857
!(assertEqual
  (evidence-toStrength (evidence 12 2))
  (/ 12 14))

;; Strength of individual links
!(assertEqual (evidence-toStrength (leak-to-wall)) 0.8)
!(assertEqual (evidence-toStrength (wall-to-mold)) 0.6)

;;; ============================================================
;;; Test 4: Revision commutativity across all motifs
;;; ============================================================
!(println! "=== Commutativity Tests ===")

!(assertEqual
  (evidence-hplus (shower-evidence) (leak-evidence))
  (evidence-hplus (leak-evidence) (shower-evidence)))

!(assertEqual
  (evidence-hplus (motion-evidence) (power-evidence))
  (evidence-hplus (power-evidence) (motion-evidence)))

!(println! "All BN motif tests passed.")
