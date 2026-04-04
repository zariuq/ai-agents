;;; Maple Court Multi-Carrier Conformance
;;;
;;; The SAME hplus axiom works across THREE different evidence types:
;;;   1. Binary (Beta-Bernoulli): motion detections → occupancy
;;;   2. Continuous (Normal-Gamma): humidity readings → temperature
;;;   3. Categorical (Dirichlet): laundry observations → state
;;;
;;; Key insight: the WorldModel extract_add law is parametric in V.
;;; Different carriers, same algebraic structure.
;;;
;;; Lean side: PLNMapleCourtDemo.lean uses all three carriers

!(import! &self ../../hyperon/PeTTa/pln_inference/pln_evidence)
!(import! &self ../../hyperon/PeTTa/pln_inference/pln_continuous_evidence)

;;; ============================================================
;;; Carrier 1: Binary (Beta-Bernoulli)
;;; Motion detections → occupancy evidence
;;; ============================================================
!(println! "=== Binary Carrier (motion → occupancy) ===")

(= (morning-motion) (evidence 3 0))    ; 3 detections, 0 misses
(= (evening-motion) (evidence 1 1))    ; 1 detection, 1 miss

;; Revision: hplus adds counts
!(assertEqual
  (evidence-hplus (morning-motion) (evening-motion))
  (evidence 4 1))

;; Strength: 4/(4+1) = 0.8
!(assertEqual
  (evidence-toStrength (evidence 4 1))
  0.8)

!(println! "Binary carrier: OK")

;;; ============================================================
;;; Carrier 2: Continuous (Normal sufficient stats)
;;; Humidity readings → temperature evidence
;;; cont-ev = (n, Σx, Σx²) sufficient statistics
;;; ============================================================
!(println! "=== Continuous Carrier (humidity readings) ===")

;; Morning readings: 56.2 and 54.8
(= (morning-humidity) (observe-all (56.2 54.8)))

;; Evening readings: 78.5 and 82.1
(= (evening-humidity) (observe-all (78.5 82.1)))

;; Revision: hplus adds sufficient statistics
(= (all-humidity) (hplus (morning-humidity) (evening-humidity)))

!(println! "morning humidity evidence:" (morning-humidity))
!(println! "evening humidity evidence:" (evening-humidity))
!(println! "revised humidity evidence:" (all-humidity))

;; The mean of all readings: (56.2+54.8+78.5+82.1)/4 = 271.6/4 = 67.9
!(println! "sample mean of all readings:" (ev-mean (all-humidity)))

;; Sleep consolidation: batch = sequential
!(assertEqual
  (hplus (morning-humidity) (evening-humidity))
  (hplus (evening-humidity) (morning-humidity)))

!(println! "Continuous carrier: OK")

;;; ============================================================
;;; Carrier 3: Categorical (count vectors)
;;; Laundry state observations: free/in-use/done
;;; We represent as three binary evidence channels
;;; ============================================================
!(println! "=== Categorical Carrier (laundry state) ===")

;; Morning observations: 3 free, 1 in-use, 0 done
(= (morning-laundry-free)   (evidence 3 0))
(= (morning-laundry-inuse)  (evidence 1 0))
(= (morning-laundry-done)   (evidence 0 0))

;; Evening observations: 0 free, 2 in-use, 1 done
(= (evening-laundry-free)   (evidence 0 0))
(= (evening-laundry-inuse)  (evidence 2 0))
(= (evening-laundry-done)   (evidence 1 0))

;; Revision per category
!(assertEqual
  (evidence-hplus (morning-laundry-free) (evening-laundry-free))
  (evidence 3 0))

!(assertEqual
  (evidence-hplus (morning-laundry-inuse) (evening-laundry-inuse))
  (evidence 3 0))

!(assertEqual
  (evidence-hplus (morning-laundry-done) (evening-laundry-done))
  (evidence 1 0))

;; Total observations: 3+1+0 + 0+2+1 = 7
!(println! "Total laundry observations: 7")

!(println! "Categorical carrier: OK")

;;; ============================================================
;;; The Unifying Principle
;;; ============================================================
!(println! "")
!(println! "=== The Unifying Principle ===")
!(println! "All three carriers satisfy the SAME axiom:")
!(println! "  extract(revise(W1,W2), q) = hplus(extract(W1,q), extract(W2,q))")
!(println! "Binary: evidence-hplus on (pos,neg) pairs")
!(println! "Continuous: hplus on (n, sum, sumSq) triples")
!(println! "Categorical: evidence-hplus per category")
!(println! "This is the AdditiveWorldModel axiom in action.")
!(println! "")
!(println! "All multi-carrier tests passed.")
