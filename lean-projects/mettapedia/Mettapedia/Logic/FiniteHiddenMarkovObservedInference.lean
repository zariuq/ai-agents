import Mettapedia.Logic.FiniteHiddenMarkovModel
import Mettapedia.Logic.MarkovDeFinettiMomentProblem

/-!
# Observed-Only Inference for Finite Hidden Markov Models

This file formalizes the first honest observed-only inference layer for finite
HMMs:

* backward messages,
* initial-state backward decomposition of the observed-word law,
* forward terminal-state masses,
* the filtering mass identity.

Positive example:
* the observed-word probability is the sum of terminal latent-state masses.

Negative example:
* this does not yet claim full smoothing or hidden-state posterior recovery as
  an additive WM carrier.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Logic.FiniteHiddenMarkovObservedInference

open Mettapedia.Logic
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.FiniteHiddenMarkovModel
open scoped BigOperators ENNReal NNReal

variable {latent obs : ℕ}

lemma ofFn_snoc {α : Type*} {n : ℕ} (a : α) (g : Fin n → α) :
    List.ofFn (Fin.snoc g a) = List.ofFn g ++ [a] := by
  have hlist : List.ofFn (Fin.snoc g a) = (List.ofFn g).concat a := by
    simpa [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last] using
      (List.ofFn_succ' (f := Fin.snoc g a))
  rw [hlist]
  simp [List.concat_eq_append]

/-! ## Backward messages -/

/-- Backward continuation mass from a current latent state. -/
def backwardMessage (θ : FiniteHMMParam latent obs) :
    Fin latent → List (Fin obs) → ℝ≥0∞
  | _, [] => 1
  | x, y :: ys =>
      ∑ x' : Fin latent,
        (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
          (emissionProb θ x' y : ℝ≥0∞) *
            backwardMessage θ x' ys

@[simp] theorem backwardMessage_nil
    (θ : FiniteHMMParam latent obs) (x : Fin latent) :
    backwardMessage θ x [] = 1 := rfl

@[simp] theorem backwardMessage_cons
    (θ : FiniteHMMParam latent obs) (x : Fin latent)
    (y : Fin obs) (ys : List (Fin obs)) :
    backwardMessage θ x (y :: ys) =
      ∑ x' : Fin latent,
        (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
          (emissionProb θ x' y : ℝ≥0∞) *
            backwardMessage θ x' ys := rfl

/-- Backward message as the explicit latent-tail sum under `wordProbAux`. -/
theorem backwardMessage_eq_sum_wordProbAux_observationWeight
    (θ : FiniteHMMParam latent obs) (x : Fin latent) :
    ∀ ys : List (Fin obs),
      backwardMessage θ x ys =
        ∑ xs : Fin ys.length → Fin latent,
          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
            observationWeight θ (List.ofFn xs) ys
  | [] => by
      simp [backwardMessage, MarkovDeFinettiHard.wordProbAux]
  | y :: ys => by
      let n := ys.length
      change backwardMessage θ x (y :: ys) =
        ∑ xs : Fin (n + 1) → Fin latent,
          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
            observationWeight θ (List.ofFn xs) (y :: ys)
      have hdecomp :
          (∑ xs : Fin (n + 1) → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) (y :: ys)) =
            ∑ p : Fin latent × (Fin n → Fin latent),
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn (Fin.cons p.1 p.2)) :
                  ℝ≥0∞) *
                observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys) := by
        simpa [n] using
          (Fintype.sum_equiv
            (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Fin latent))
            (fun p : Fin latent × (Fin n → Fin latent) =>
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn (Fin.cons p.1 p.2)) :
                  ℝ≥0∞) *
                observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys))
            (fun xs : Fin (n + 1) → Fin latent =>
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) (y :: ys))
            (fun _ => rfl)).symm
      rw [backwardMessage_cons, hdecomp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro x' hx'
      rw [backwardMessage_eq_sum_wordProbAux_observationWeight θ x' ys]
      have hmul :
          (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
              (emissionProb θ x' y : ℝ≥0∞) *
                ∑ xs : Fin n → Fin latent,
                  (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                    observationWeight θ (List.ofFn xs) ys =
            ∑ xs : Fin n → Fin latent,
              (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                ((emissionProb θ x' y : ℝ≥0∞) *
                  ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                    observationWeight θ (List.ofFn xs) ys)) := by
        calc
          ((stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
              (emissionProb θ x' y : ℝ≥0∞)) *
              ∑ xs : Fin n → Fin latent,
                (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                  observationWeight θ (List.ofFn xs) ys
            =
              ∑ xs : Fin n → Fin latent,
                ((stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                  (emissionProb θ x' y : ℝ≥0∞)) *
                    ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                      observationWeight θ (List.ofFn xs) ys) := by
                        simpa using
                          (Finset.mul_sum
                            (s := (Finset.univ : Finset (Fin n → Fin latent)))
                            (a := (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                              (emissionProb θ x' y : ℝ≥0∞))
                            (f := fun xs : Fin n → Fin latent =>
                              (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) :
                                  ℝ≥0∞) *
                                observationWeight θ (List.ofFn xs) ys))
          _ =
              ∑ xs : Fin n → Fin latent,
                (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                  ((emissionProb θ x' y : ℝ≥0∞) *
                    ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                      observationWeight θ (List.ofFn xs) ys)) := by
                        refine Finset.sum_congr rfl ?_
                        intro xs hxs
                        simp [mul_assoc]
      calc
        (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
            (emissionProb θ x' y : ℝ≥0∞) *
            ∑ xs : Fin n → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys
          =
            ∑ xs : Fin n → Fin latent,
              (stepProb (k := latent) θ.latentParam x x' : ℝ≥0∞) *
                ((emissionProb θ x' y : ℝ≥0∞) *
                  ((wordProbAux (k := latent) θ.latentParam x' (List.ofFn xs) : ℝ≥0∞) *
                    observationWeight θ (List.ofFn xs) ys)) := hmul
        _ =
            ∑ xs : Fin n → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn (Fin.cons x' xs)) :
                  ℝ≥0∞) *
                observationWeight θ (List.ofFn (Fin.cons x' xs)) (y :: ys) := by
                  refine Finset.sum_congr rfl ?_
                  intro xs hxs
                  simp [MarkovDeFinettiHard.wordProbAux,
                    mul_assoc, mul_left_comm, mul_comm]

/-- The observed-word law decomposes through the initial latent state and the
backward continuation message. -/
theorem observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
    (θ : FiniteHMMParam latent obs) (y : Fin obs) (ys : List (Fin obs)) :
    observedWordProb θ (y :: ys) =
      ∑ x : Fin latent,
        (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
          (emissionProb θ x y : ℝ≥0∞) *
            backwardMessage θ x ys := by
  let n := ys.length
  have hdecomp :
      observedWordProb θ (y :: ys) =
        ∑ p : Fin latent × (Fin n → Fin latent),
          wordProb (k := latent) θ.latentParam (List.ofFn (Fin.cons p.1 p.2)) *
            observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys) := by
    unfold observedWordProb
    simpa [n] using
      (Fintype.sum_equiv
        (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Fin latent))
        (fun p : Fin latent × (Fin n → Fin latent) =>
          wordProb (k := latent) θ.latentParam (List.ofFn (Fin.cons p.1 p.2)) *
            observationWeight θ (List.ofFn (Fin.cons p.1 p.2)) (y :: ys))
        (fun xs : Fin (n + 1) → Fin latent =>
          wordProb (k := latent) θ.latentParam (List.ofFn xs) *
            observationWeight θ (List.ofFn xs) (y :: ys))
        (fun _ => rfl)).symm
  rw [hdecomp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x hx
  symm
  rw [backwardMessage_eq_sum_wordProbAux_observationWeight θ x ys]
  have hmul :
      (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
          (emissionProb θ x y : ℝ≥0∞) *
            ∑ xs : Fin n → Fin latent,
              (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys =
        ∑ xs : Fin n → Fin latent,
          (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
            ((emissionProb θ x y : ℝ≥0∞) *
              ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys)) := by
    calc
      ((initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
          (emissionProb θ x y : ℝ≥0∞)) *
          ∑ xs : Fin n → Fin latent,
            (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
              observationWeight θ (List.ofFn xs) ys
        =
          ∑ xs : Fin n → Fin latent,
            ((initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
              (emissionProb θ x y : ℝ≥0∞)) *
                ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                  observationWeight θ (List.ofFn xs) ys) := by
                    simpa using
                      (Finset.mul_sum
                        (s := (Finset.univ : Finset (Fin n → Fin latent)))
                        (a := (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
                          (emissionProb θ x y : ℝ≥0∞))
                        (f := fun xs : Fin n → Fin latent =>
                          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) :
                              ℝ≥0∞) *
                            observationWeight θ (List.ofFn xs) ys))
      _ =
          ∑ xs : Fin n → Fin latent,
            (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
              ((emissionProb θ x y : ℝ≥0∞) *
                ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                  observationWeight θ (List.ofFn xs) ys)) := by
                    refine Finset.sum_congr rfl ?_
                    intro xs hxs
                    simp [mul_assoc]
  calc
    (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
        (emissionProb θ x y : ℝ≥0∞) *
        ∑ xs : Fin n → Fin latent,
          (wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
            observationWeight θ (List.ofFn xs) ys
      =
        ∑ xs : Fin n → Fin latent,
          (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
            ((emissionProb θ x y : ℝ≥0∞) *
              ((wordProbAux (k := latent) θ.latentParam x (List.ofFn xs) : ℝ≥0∞) *
                observationWeight θ (List.ofFn xs) ys)) := hmul
    _ =
        ∑ xs : Fin n → Fin latent,
          wordProb (k := latent) θ.latentParam (List.ofFn (Fin.cons x xs)) *
            observationWeight θ (List.ofFn (Fin.cons x xs)) (y :: ys) := by
              refine Finset.sum_congr rfl ?_
              intro xs hxs
              simp [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
                mul_assoc, mul_left_comm, mul_comm]

/-! ## Forward terminal-state masses -/

/-- Forward message: joint mass of an observed word together with the event
that the final latent state equals `x`. -/
def forwardMessage (θ : FiniteHMMParam latent obs) :
    List (Fin obs) → Fin latent → ℝ≥0∞
  | [], x => (initProb (k := latent) θ.latentParam x : ℝ≥0∞)
  | y :: ys, x =>
      ∑ xs : Fin ys.length → Fin latent,
        wordProb (k := latent) θ.latentParam (List.ofFn xs ++ [x]) *
          observationWeight θ (List.ofFn xs ++ [x]) (y :: ys)

@[simp] theorem forwardMessage_nil
    (θ : FiniteHMMParam latent obs) (x : Fin latent) :
    forwardMessage θ [] x = (initProb (k := latent) θ.latentParam x : ℝ≥0∞) := rfl

@[simp] theorem forwardMessage_singleton
    (θ : FiniteHMMParam latent obs) (y : Fin obs) (x : Fin latent) :
    forwardMessage θ [y] x =
      (initProb (k := latent) θ.latentParam x : ℝ≥0∞) *
        (emissionProb θ x y : ℝ≥0∞) := by
  simp [forwardMessage, MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
    MarkovDeFinettiHard.wordProbAux, observationWeight]

/-- The observed-word law is the terminal-state sum of the forward message. -/
theorem observedWordProb_eq_sum_forwardMessage
    (θ : FiniteHMMParam latent obs) :
    ∀ ys : List (Fin obs),
      observedWordProb θ ys = ∑ x : Fin latent, forwardMessage θ ys x
  | [] => by
      rw [observedWordProb_nil]
      simp [forwardMessage, initProb_sum_enn]
  | y :: ys => by
      let n := ys.length
      have hdecomp :
          observedWordProb θ (y :: ys) =
            ∑ p : Fin latent × (Fin n → Fin latent),
              wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc p.2 p.1)) *
                observationWeight θ (List.ofFn (Fin.snoc p.2 p.1)) (y :: ys) := by
        unfold observedWordProb
        simpa [n] using
          (Fintype.sum_equiv
            (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin latent))
            (fun p : Fin latent × (Fin n → Fin latent) =>
              wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc p.2 p.1)) *
                observationWeight θ (List.ofFn (Fin.snoc p.2 p.1)) (y :: ys))
            (fun xs : Fin (n + 1) → Fin latent =>
              wordProb (k := latent) θ.latentParam (List.ofFn xs) *
                observationWeight θ (List.ofFn xs) (y :: ys))
            (fun _ => rfl)).symm
      rw [hdecomp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hsnoc :
          ∑ xs : Fin n → Fin latent,
            wordProb (k := latent) θ.latentParam (List.ofFn (Fin.snoc xs x)) *
              observationWeight θ (List.ofFn (Fin.snoc xs x)) (y :: ys) =
            ∑ xs : Fin n → Fin latent,
              wordProb (k := latent) θ.latentParam (List.ofFn xs ++ [x]) *
                observationWeight θ (List.ofFn xs ++ [x]) (y :: ys) := by
        refine Finset.sum_congr rfl ?_
        intro xs hxs
        rw [ofFn_snoc (a := x) (g := xs)]
      simpa [forwardMessage] using hsnoc

/-! ## Filtering masses -/

/-- Unnormalized filtering mass at the final latent state after observing the
prefix `ys`. -/
def filteringMass (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (x : Fin latent) : ℝ≥0∞ :=
  forwardMessage θ ys x

theorem filteringMass_sum_eq_observedWordProb
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs)) :
    ∑ x : Fin latent, filteringMass θ ys x = observedWordProb θ ys := by
  simpa [filteringMass] using (observedWordProb_eq_sum_forwardMessage θ ys).symm

/-- Observed-word probabilities are finite, since they are cylinder masses under
the observed sequence probability measure. -/
theorem observedWordProb_ne_top
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs)) :
    observedWordProb θ ys ≠ ⊤ := by
  rw [← observedSequenceMeasure_cylinder_eq_observedWordProb (latent := latent) (obs := obs)
    (θ := θ) ys]
  have hmono :
      observedSequenceMeasure (latent := latent) (obs := obs) θ
        (MarkovDeFinettiRecurrence.cylinder (k := obs) ys) ≤
      observedSequenceMeasure (latent := latent) (obs := obs) θ Set.univ := by
    exact MeasureTheory.measure_mono (by intro ω hω; simp)
  exact ne_top_of_le_ne_top (by simp) hmono

/-- Normalized filtering posterior mass at the final latent state after
observing the prefix `ys`. -/
def filteringPosteriorMass (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (x : Fin latent) : ℝ≥0∞ :=
  filteringMass θ ys x / observedWordProb θ ys

theorem filteringPosteriorMass_sum_eq_one
    (θ : FiniteHMMParam latent obs) (ys : List (Fin obs))
    (hys : observedWordProb θ ys ≠ 0) :
    ∑ x : Fin latent, filteringPosteriorMass θ ys x = 1 := by
  have htop : observedWordProb θ ys ≠ ⊤ := observedWordProb_ne_top (θ := θ) ys
  unfold filteringPosteriorMass
  calc
    ∑ x : Fin latent, filteringMass θ ys x / observedWordProb θ ys
      = ∑ x : Fin latent, filteringMass θ ys x * (observedWordProb θ ys)⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑ x : Fin latent, filteringMass θ ys x) * (observedWordProb θ ys)⁻¹ := by
          rw [Finset.sum_mul]
    _ = observedWordProb θ ys * (observedWordProb θ ys)⁻¹ := by
          rw [filteringMass_sum_eq_observedWordProb]
    _ = 1 := ENNReal.mul_inv_cancel hys htop

/-! ## Smoothing masses -/

/-- Probability of appending a latent tail after a fixed terminal latent state. -/
theorem wordProbAux_append_terminal
    (θ : MarkovParam latent) (a x : Fin latent) :
    ∀ xs zs : List (Fin latent),
      (wordProbAux (k := latent) θ a ((xs ++ [x]) ++ zs) : ℝ≥0∞) =
        (wordProbAux (k := latent) θ a (xs ++ [x]) : ℝ≥0∞) *
          (wordProbAux (k := latent) θ x zs : ℝ≥0∞)
  | [], zs => by
      simp [MarkovDeFinettiHard.wordProbAux]
  | b :: xs, zs => by
      simp only [MarkovDeFinettiHard.wordProbAux, List.cons_append, ENNReal.coe_mul]
      rw [wordProbAux_append_terminal (θ := θ) (a := b) (x := x) (xs := xs) (zs := zs)]
      ac_rfl

/-- Appending a latent tail and an observed tail factors the observation
likelihood when the split boundary is aligned by length. -/
theorem observationWeight_append_of_length_eq
    (θ : FiniteHMMParam latent obs) :
    ∀ xs : List (Fin latent), ∀ zs : List (Fin obs),
      xs.length = zs.length →
      ∀ ys : List (Fin latent), ∀ us : List (Fin obs),
        observationWeight θ (xs ++ ys) (zs ++ us) =
          observationWeight θ xs zs * observationWeight θ ys us
  | [], [], hlen, ys, us => by
      simp [FiniteHiddenMarkovModel.observationWeight]
  | [], z :: zs, hlen, ys, us => by
      cases hlen
  | x :: xs, [], hlen, ys, us => by
      cases hlen
  | x :: xs, z :: zs, hlen, ys, us => by
      have htail : xs.length = zs.length := Nat.succ.inj hlen
      simp [FiniteHiddenMarkovModel.observationWeight,
        observationWeight_append_of_length_eq (θ := θ) (xs := xs) (zs := zs) (ys := ys)
          (us := us) htail,
        mul_assoc]

/-- Probability of a latent word split at a marked terminal state. -/
theorem wordProb_append_terminal
    (θ : MarkovParam latent) (x : Fin latent) :
    ∀ xs zs : List (Fin latent),
      wordProb (k := latent) θ ((xs ++ [x]) ++ zs) =
        wordProb (k := latent) θ (xs ++ [x]) *
          (wordProbAux (k := latent) θ x zs : ℝ≥0∞)
  | [], zs => by
      simp [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
        MarkovDeFinettiHard.wordProbAux]
  | a :: xs, zs => by
      simp only [MarkovDeFinettiHard.wordProb, MarkovDeFinettiHard.wordProbNN,
        List.cons_append, ENNReal.coe_mul]
      rw [wordProbAux_append_terminal (θ := θ) (a := a) (x := x) (xs := xs) (zs := zs)]
      ac_rfl

/-- Unnormalized smoothing mass for a split observed word: the mass of all
latent trajectories whose state at the split point is `x`. -/
def smoothingMass (θ : FiniteHMMParam latent obs)
    (ys : List (Fin obs)) (zs : List (Fin obs)) (x : Fin latent) : ℝ≥0∞ :=
  forwardMessage θ ys x * backwardMessage θ x zs

/-- At a singleton observation prefix, smoothing masses sum to the full
observed-word probability across the split. This is the first honest
forward/backward total-mass identity. -/
theorem smoothingMass_sum_eq_observedWordProb_singleton
    (θ : FiniteHMMParam latent obs) (y : Fin obs) (zs : List (Fin obs)) :
    ∑ x : Fin latent, smoothingMass θ [y] zs x =
      observedWordProb θ (y :: zs) := by
  rw [observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
    (θ := θ) (y := y) (ys := zs)]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [smoothingMass, forwardMessage_singleton]

/-! ## Observed-only boundary: hidden-label nonidentifiability -/

private def diracPM {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) : MeasureTheory.ProbabilityMeasure α :=
  ⟨MeasureTheory.Measure.dirac a, MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

/-- Hidden state `0` is the live state, and emits observation `0`
deterministically. -/
private def hiddenLabelSwapHMM₀ : FiniteHMMParam 2 2 where
  latentParam :=
    { init := diracPM 0
      trans := fun i => diracPM i }
  emission := fun
    | 0 => diracPM 0
    | 1 => diracPM 1

/-- Same observed process as `hiddenLabelSwapHMM₀`, but with the hidden labels
swapped. -/
private def hiddenLabelSwapHMM₁ : FiniteHMMParam 2 2 where
  latentParam :=
    { init := diracPM 1
      trans := fun i => diracPM i }
  emission := fun
    | 0 => diracPM 1
    | 1 => diracPM 0

/-- Positive example: the two label-swapped HMMs agree on the observed
probability of the singleton word `[0]`. -/
theorem hiddenLabelSwap_observedWordProb_singleton :
    observedWordProb hiddenLabelSwapHMM₀ [0] =
      observedWordProb hiddenLabelSwapHMM₁ [0] := by
  rw [observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
      (θ := hiddenLabelSwapHMM₀) (y := 0) (ys := []),
    observedWordProb_cons_eq_sum_init_mul_emission_mul_backward
      (θ := hiddenLabelSwapHMM₁) (y := 0) (ys := [])]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [backwardMessage_nil]
  change
    ((((initProb hiddenLabelSwapHMM₀.latentParam 0 * emissionProb hiddenLabelSwapHMM₀ 0 0) +
        (initProb hiddenLabelSwapHMM₀.latentParam 1 * emissionProb hiddenLabelSwapHMM₀ 1 0) :
          ℝ≥0) : ℝ≥0∞) =
      (((initProb hiddenLabelSwapHMM₁.latentParam 0 * emissionProb hiddenLabelSwapHMM₁ 0 0) +
        (initProb hiddenLabelSwapHMM₁.latentParam 1 * emissionProb hiddenLabelSwapHMM₁ 1 0) :
          ℝ≥0) : ℝ≥0∞))
  rw [ENNReal.coe_inj]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₀, hiddenLabelSwapHMM₁, diracPM]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := by
    change Set.singleton (0 : Fin 2) 0
    rfl
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    change ¬ Set.singleton (0 : Fin 2) 1
    intro h
    cases h
  have h01 : (0 : Fin 2) ∉ Set.singleton (1 : Fin 2) := by
    change ¬ Set.singleton (1 : Fin 2) 0
    intro h
    cases h
  have h11 : (1 : Fin 2) ∈ Set.singleton (1 : Fin 2) := by
    change Set.singleton (1 : Fin 2) 1
    rfl
  simp [h00, h10, h01, h11]

/-- Positive example: under the first model, seeing a `0` places all
unnormalized filtering mass on hidden state `0`. -/
theorem hiddenLabelSwap_forwardMessage_state0_model0 :
    forwardMessage hiddenLabelSwapHMM₀ [0] 0 = 1 := by
  rw [forwardMessage_singleton]
  change (((initProb hiddenLabelSwapHMM₀.latentParam 0 * emissionProb hiddenLabelSwapHMM₀ 0 0 :
      ℝ≥0) : ℝ≥0∞) = 1)
  rw [ENNReal.coe_eq_one]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₀, diracPM]
  have h00 : (0 : Fin 2) ∈ Set.singleton (0 : Fin 2) := by
    change Set.singleton (0 : Fin 2) 0
    rfl
  simp [h00]

/-- Under the first model, the same singleton observation puts zero
unnormalized filtering mass on hidden state `1`. -/
theorem hiddenLabelSwap_forwardMessage_state1_model0 :
    forwardMessage hiddenLabelSwapHMM₀ [0] 1 = 0 := by
  rw [forwardMessage_singleton]
  change (((initProb hiddenLabelSwapHMM₀.latentParam 1 * emissionProb hiddenLabelSwapHMM₀ 1 0 :
      ℝ≥0) : ℝ≥0∞) = 0)
  rw [ENNReal.coe_eq_zero]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₀, diracPM]
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    change ¬ Set.singleton (0 : Fin 2) 1
    intro h
    cases h
  simp [h10]

/-- Under the first model, the observed singleton `[0]` has probability `1`. -/
theorem hiddenLabelSwap_observedWordProb_singleton_model0 :
    observedWordProb hiddenLabelSwapHMM₀ [0] = 1 := by
  rw [observedWordProb_eq_sum_forwardMessage, Fin.sum_univ_two,
    hiddenLabelSwap_forwardMessage_state0_model0,
    hiddenLabelSwap_forwardMessage_state1_model0]
  simp

/-- Negative example: under the label-swapped model, the same observation `0`
places zero filtering mass on hidden state `0`. -/
theorem hiddenLabelSwap_forwardMessage_state0_model1 :
    forwardMessage hiddenLabelSwapHMM₁ [0] 0 = 0 := by
  rw [forwardMessage_singleton]
  change (((initProb hiddenLabelSwapHMM₁.latentParam 0 * emissionProb hiddenLabelSwapHMM₁ 0 0 :
      ℝ≥0) : ℝ≥0∞) = 0)
  rw [ENNReal.coe_eq_zero]
  simp [initProb, emissionProb, hiddenLabelSwapHMM₁, diracPM]
  have h10 : (1 : Fin 2) ∉ Set.singleton (0 : Fin 2) := by
    change ¬ Set.singleton (0 : Fin 2) 1
    intro h
    cases h
  simp [h10]

/-- Positive example: when the observed singleton has positive mass, the
filtering posterior normalizes to total mass `1`. -/
theorem hiddenLabelSwap_filteringPosterior_sum_model0 :
    ∑ x : Fin 2, filteringPosteriorMass hiddenLabelSwapHMM₀ [0] x = 1 := by
  apply filteringPosteriorMass_sum_eq_one
  rw [hiddenLabelSwap_observedWordProb_singleton_model0]
  simp

/-- Positive example: singleton-prefix smoothing recovers the corresponding full
observed-word probability across the split. -/
theorem hiddenLabelSwap_smoothing_singleton_model0 :
    ∑ x : Fin 2, smoothingMass hiddenLabelSwapHMM₀ [0] [0] x =
      observedWordProb hiddenLabelSwapHMM₀ [0, 0] := by
  simpa using
    (smoothingMass_sum_eq_observedWordProb_singleton
      (θ := hiddenLabelSwapHMM₀) (y := 0) (zs := [0]))

/-- Honest observed-only boundary: even matching observed probability for a
concrete observation word does not determine the label-indexed filtering mass. -/
theorem exists_same_observedWordProb_different_forwardMessage :
    ∃ θ₀ θ₁ : FiniteHMMParam 2 2,
      observedWordProb θ₀ [0] = observedWordProb θ₁ [0] ∧
        forwardMessage θ₀ [0] 0 ≠ forwardMessage θ₁ [0] 0 := by
  refine ⟨hiddenLabelSwapHMM₀, hiddenLabelSwapHMM₁, hiddenLabelSwap_observedWordProb_singleton, ?_⟩
  rw [hiddenLabelSwap_forwardMessage_state0_model0,
    hiddenLabelSwap_forwardMessage_state0_model1]
  simp

end Mettapedia.Logic.FiniteHiddenMarkovObservedInference
