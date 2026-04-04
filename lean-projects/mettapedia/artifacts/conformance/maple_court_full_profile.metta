;;; Maple Court Full Profile Conformance
;;;
;;; Extracts ALL 9 query types from ONE composite full-day state.
;;; Three carriers: Binary (Beta), Categorical (Dirichlet), Continuous (skip).
;;;
;;; This is the PeTTa mirror of PLNMapleCourtDemo.lean's fullDay_* theorems.
;;; Every assertEqual value here matches a kernel-checked Lean theorem.
;;;
;;; Lean side: PLNMapleCourtDemo.lean (45 theorems, 0 sorry)
;;;   fullDay_roomOccupied, fullDay_showerRunning, fullDay_pipeLeak,
;;;   fullDay_laundryFree, fullDay_laundryBusy, fullDay_laundryFull,
;;;   fullDay_elevatorNormal, fullDay_elevatorSlow, fullDay_elevatorFaulty

!(import! &self ../../hyperon/PeTTa/pln_inference/pln_evidence)
!(import! &self ../../hyperon/PeTTa/pln_inference/dirichlet_categorical)

;;; ============================================================
;;; Helper: Dirichlet → Binary projection
;;; Matches Lean's dirichletToBinary:
;;;   pos = counts[i], neg = total - counts[i]
;;; ============================================================

(= (dirichlet-to-binary $kev $i)
   (let* (($pos (k-evidence-count $kev $i))
          ($total (k-evidence-total $kev))
          ($neg (- $total $pos)))
     (evidence $pos $neg)))

;;; ============================================================
;;; Morning Observations (matching Lean's morningState)
;;; ============================================================
;;; Apartment: 3 motion detections, no leak, no shower
;;; Building: laundry=free, elevator=normal

(= (morning-roomOccupied)  (evidence 3 0))
(= (morning-showerRunning) (evidence 0 0))
(= (morning-pipeLeak)      (evidence 0 0))
(= (morning-laundry) (k-evidence (1 0 0)))   ; free
(= (morning-elevator) (k-evidence (1 0 0)))   ; normal

;;; ============================================================
;;; Evening Observations (matching Lean's eveningState)
;;; ============================================================
;;; Apartment: 1 motion, 1 leak, 1 shower
;;; Building: laundry=busy, elevator=normal

(= (evening-roomOccupied)  (evidence 1 0))
(= (evening-showerRunning) (evidence 1 0))
(= (evening-pipeLeak)      (evidence 1 0))
(= (evening-laundry) (k-evidence (0 1 0)))   ; busy
(= (evening-elevator) (k-evidence (1 0 0)))   ; normal

;;; ============================================================
;;; Full Day: Revision (morning + evening)
;;; ============================================================

(= (fullday-roomOccupied)  (evidence-hplus (morning-roomOccupied)  (evening-roomOccupied)))
(= (fullday-showerRunning) (evidence-hplus (morning-showerRunning) (evening-showerRunning)))
(= (fullday-pipeLeak)      (evidence-hplus (morning-pipeLeak)      (evening-pipeLeak)))
(= (fullday-laundry)  (k-revision (morning-laundry)  (evening-laundry)))
(= (fullday-elevator) (k-revision (morning-elevator) (evening-elevator)))

;;; ============================================================
;;; Test 1: Binary Queries (3 tests)
;;; ============================================================
!(println! "=== Binary Queries ===")

;; roomOccupied: 3+1 = 4 pos, 0+0 = 0 neg
!(assertEqual (fullday-roomOccupied) (evidence 4 0))

;; showerRunning: 0+1 = 1 pos, 0+0 = 0 neg
!(assertEqual (fullday-showerRunning) (evidence 1 0))

;; pipeLeak: 0+1 = 1 pos, 0+0 = 0 neg
!(assertEqual (fullday-pipeLeak) (evidence 1 0))

!(println! "Binary queries: OK")

;;; ============================================================
;;; Test 2: Categorical Queries via dirichlet-to-binary (6 tests)
;;; ============================================================
!(println! "=== Categorical Queries ===")

;; Verify revision: laundry (1,0,0) + (0,1,0) = (1,1,0)
!(assertEqual (fullday-laundry) (k-evidence (1 1 0)))

;; Verify revision: elevator (1,0,0) + (1,0,0) = (2,0,0)
!(assertEqual (fullday-elevator) (k-evidence (2 0 0)))

;; Laundry: free (index 0) → pos=1, neg=2-1=1 → (1,1)
!(assertEqual (dirichlet-to-binary (fullday-laundry) 0) (evidence 1 1))

;; Laundry: busy (index 1) → pos=1, neg=2-1=1 → (1,1)
!(assertEqual (dirichlet-to-binary (fullday-laundry) 1) (evidence 1 1))

;; Laundry: full (index 2) → pos=0, neg=2-0=2 → (0,2)
!(assertEqual (dirichlet-to-binary (fullday-laundry) 2) (evidence 0 2))

;; Elevator: normal (index 0) → pos=2, neg=2-2=0 → (2,0)
!(assertEqual (dirichlet-to-binary (fullday-elevator) 0) (evidence 2 0))

;; Elevator: slow (index 1) → pos=0, neg=2-0=2 → (0,2)
!(assertEqual (dirichlet-to-binary (fullday-elevator) 1) (evidence 0 2))

;; Elevator: faulty (index 2) → pos=0, neg=2-0=2 → (0,2)
!(assertEqual (dirichlet-to-binary (fullday-elevator) 2) (evidence 0 2))

!(println! "Categorical queries: OK")

;;; ============================================================
;;; Test 3: Strength values (9 tests)
;;; ============================================================
!(println! "=== Strength Values ===")

;; Binary strengths
!(assertEqual (evidence-toStrength (fullday-roomOccupied)) 1.0)
!(assertEqual (evidence-toStrength (fullday-showerRunning)) 1.0)
!(assertEqual (evidence-toStrength (fullday-pipeLeak)) 1.0)

;; Categorical strengths (via dirichlet-to-binary projection)
!(assertEqual (evidence-toStrength (dirichlet-to-binary (fullday-laundry) 0)) 0.5)
!(assertEqual (evidence-toStrength (dirichlet-to-binary (fullday-laundry) 1)) 0.5)
!(assertEqual (evidence-toStrength (dirichlet-to-binary (fullday-laundry) 2)) 0.0)
!(assertEqual (evidence-toStrength (dirichlet-to-binary (fullday-elevator) 0)) 1.0)
!(assertEqual (evidence-toStrength (dirichlet-to-binary (fullday-elevator) 1)) 0.0)
!(assertEqual (evidence-toStrength (dirichlet-to-binary (fullday-elevator) 2)) 0.0)

!(println! "Strength values: OK")

;;; ============================================================
;;; Test 4: Evidence compositionality (evidence_add)
;;; ============================================================
!(println! "=== Compositionality ===")

;; Binary: hplus(morning, evening) = fullday (already tested above)

;; Categorical: dirichlet-to-binary of revision = hplus of projections
;; This mirrors Lean's evidence_add_laundryInState theorem
!(assertEqual
  (dirichlet-to-binary (k-revision (morning-laundry) (evening-laundry)) 0)
  (evidence-hplus (dirichlet-to-binary (morning-laundry) 0)
                  (dirichlet-to-binary (evening-laundry) 0)))

!(assertEqual
  (dirichlet-to-binary (k-revision (morning-elevator) (evening-elevator)) 0)
  (evidence-hplus (dirichlet-to-binary (morning-elevator) 0)
                  (dirichlet-to-binary (evening-elevator) 0)))

!(println! "Compositionality: OK")

;;; ============================================================
;;; Summary
;;; ============================================================
!(println! "")
!(println! "=== Maple Court Full Profile ===")
!(println! "9 queries from ONE composite state (morning + evening)")
!(println! "3 binary: roomOccupied, showerRunning, pipeLeak")
!(println! "6 categorical: laundry {free,busy,full}, elevator {normal,slow,faulty}")
!(println! "All values match PLNMapleCourtDemo.lean fullDay_* theorems exactly.")
!(println! "All full profile tests passed.")
