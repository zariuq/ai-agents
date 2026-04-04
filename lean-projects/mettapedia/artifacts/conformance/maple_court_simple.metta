;;; Maple Court Conformance Test — Simplest Case
;;;
;;; Pipeline: runs in PeTTa, verifies evidence operations match Lean theorems.
;;;
;;; Scenario: Two observations of bathroom humidity.
;;;   Morning: sensor reports humidity high → (evidence 1 0)
;;;   Evening: sensor reports humidity low  → (evidence 0 1)
;;;   Revision: hplus(morning, evening)     = (evidence 1 1)
;;;   Strength: 1/(1+1)                     = 0.5

!(import! &self ../../hyperon/PeTTa/pln_inference/pln_evidence)

;;; === Observations (BinaryEvidence) ===
(= (morning-humidity) (evidence 1 0))
(= (evening-humidity) (evidence 0 1))

;;; === Revision: combine the two observations ===
;;; This is the WM axiom: extract(revise(W1,W2), q) = hplus(extract(W1,q), extract(W2,q))
!(println! "Test 1: evidence-hplus (revision)")
!(assertEqual
  (evidence-hplus (morning-humidity) (evening-humidity))
  (evidence 1 1))

;;; === Strength view ===
!(println! "Test 2: evidence-toStrength")
!(assertEqual
  (evidence-toStrength (evidence 1 1))
  0.5)

;;; === Commutativity: hplus is commutative ===
!(println! "Test 3: hplus commutativity")
!(assertEqual
  (evidence-hplus (evening-humidity) (morning-humidity))
  (evidence 1 1))

;;; === Zero: hplus with zero evidence ===
!(println! "Test 4: hplus with zero")
!(assertEqual
  (evidence-hplus (morning-humidity) (evidence 0 0))
  (evidence 1 0))

;;; === Multi-step revision (sleep consolidation) ===
;;; Three observations: morning + evening + night
(= (night-humidity) (evidence 2 0))

!(println! "Test 5: three-way revision (sleep consolidation)")
!(assertEqual
  (evidence-hplus (evidence-hplus (morning-humidity) (evening-humidity)) (night-humidity))
  (evidence 3 1))

;;; === Strength after three observations ===
!(println! "Test 6: strength after three observations")
!(assertEqual
  (evidence-toStrength (evidence 3 1))
  0.75)

!(println! "All Maple Court conformance tests passed.")
