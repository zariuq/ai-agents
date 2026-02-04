import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Easy Direction)

This file starts the Markov analogue of the de Finetti story.

For a finite state space `Fin k`, **Markov exchangeability** says that the probability of a finite
trajectory depends only on

* the initial state, and
* the transition-count matrix `N(a,b)` recording how many `a → b` transitions occur.

The classical theorem of Diaconis–Freedman (1980) states that Markov exchangeability is equivalent
to being a (unique) mixture of Markov chains.

In this file we prove the **easy direction**:

* a single (time-homogeneous) Markov chain induces a Markov-exchangeable `PrefixMeasure`, and
* a countable mixture of Markov-exchangeable `PrefixMeasure`s is Markov exchangeable.

This is the next tractable “domain restriction” beyond i.i.d. exchangeability: the sufficient
statistics become transition counts, and the conjugate family becomes (row-wise) Dirichlet.

The hard direction (Markov-exchangeable ⇒ mixture of Markov chains) is intentionally *not* proved
here yet; it will likely reuse the same RMK / compactness playbook as the IID `HausdorffMoment`
development, but over the compact space of stochastic matrices.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

open Finset
open Mettapedia.Logic.MarkovExchangeability
open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

namespace MarkovDeFinetti

variable {k : ℕ}

/-! ## A fixed Markov chain as a prefix measure -/

/-- A finite-state time-homogeneous Markov chain, packaged as an initial distribution and a
row-stochastic transition matrix. -/
structure MarkovChain (k : ℕ) where
  init : Fin k → ENNReal
  trans : Fin k → Fin k → ENNReal
  init_sum : (∑ a : Fin k, init a) = 1
  trans_sum : ∀ a : Fin k, (∑ b : Fin k, trans a b) = 1

namespace MarkovChain

variable (M : MarkovChain k)

/-- Product of transition probabilities along a tail, starting from a previous symbol. -/
def prefixAux (prev : Fin k) : List (Fin k) → ENNReal
  | [] => 1
  | b :: xs => M.trans prev b * prefixAux b xs

/-- Probability of a finite word under `M`, interpreted as a cylinder probability. -/
def prefixProb : List (Fin k) → ENNReal
  | [] => 1
  | a :: xs => M.init a * prefixAux M a xs

private lemma prefixAux_additive (prev : Fin k) (xs : List (Fin k)) :
    (∑ a : Fin k, prefixAux M prev (xs ++ [a])) = prefixAux M prev xs := by
  classical
  induction xs generalizing prev with
  | nil =>
      -- `prefixAux prev [a] = trans prev a`.
      simpa [prefixAux] using (M.trans_sum prev)
  | cons b xs ih =>
      -- Factor out the fixed first transition probability `trans prev b`.
      have hmul :
          (∑ a : Fin k, M.trans prev b * prefixAux M b (xs ++ [a])) =
            M.trans prev b * ∑ a : Fin k, prefixAux M b (xs ++ [a]) := by
        simpa using
          (Finset.mul_sum (a := M.trans prev b) (s := (Finset.univ : Finset (Fin k)))
              (f := fun a : Fin k => prefixAux M b (xs ++ [a]))).symm
      calc
        (∑ a : Fin k, prefixAux M prev ((b :: xs) ++ [a]))
            = ∑ a : Fin k, M.trans prev b * prefixAux M b (xs ++ [a]) := by
                simp [prefixAux, List.cons_append]
        _ = M.trans prev b * ∑ a : Fin k, prefixAux M b (xs ++ [a]) := hmul
        _ = M.trans prev b * prefixAux M b xs := by
              simp [ih]
        _ = prefixAux M prev (b :: xs) := by
              simp [prefixAux]

private lemma prefixProb_additive (xs : List (Fin k)) :
    (∑ a : Fin k, prefixProb M (xs ++ [a])) = prefixProb M xs := by
  classical
  cases xs with
  | nil =>
      -- `prefixProb [a] = init a`.
      simpa [prefixProb, prefixAux] using M.init_sum
  | cons a xs =>
      have hmul :
          (∑ b : Fin k, M.init a * prefixAux M a (xs ++ [b])) =
            M.init a * ∑ b : Fin k, prefixAux M a (xs ++ [b]) := by
        simpa using
          (Finset.mul_sum (a := M.init a) (s := (Finset.univ : Finset (Fin k)))
              (f := fun b : Fin k => prefixAux M a (xs ++ [b]))).symm
      calc
        (∑ b : Fin k, prefixProb M ((a :: xs) ++ [b]))
            = ∑ b : Fin k, M.init a * prefixAux M a (xs ++ [b]) := by
                simp [prefixProb, List.cons_append]
        _ = M.init a * ∑ b : Fin k, prefixAux M a (xs ++ [b]) := hmul
        _ = M.init a * prefixAux M a xs := by
              simp [prefixAux_additive (M := M) a xs]
        _ = prefixProb M (a :: xs) := by
              simp [prefixProb]

/-- The `FiniteAlphabet.PrefixMeasure` induced by a fixed Markov chain. -/
  noncomputable def prefixMeasure : PrefixMeasure (Fin k) :=
  { toFun := prefixProb M
    root_eq_one' := by
      simp [prefixProb]
    additive' := by
      intro xs
      simpa using (prefixProb_additive (M := M) xs) }

@[simp] theorem prefixMeasure_apply (xs : List (Fin k)) : M.prefixMeasure xs = M.prefixProb xs :=
  rfl

end MarkovChain

/-! ## Markov exchangeability of Markov chains -/

namespace MarkovChain

variable (M : MarkovChain k)

/-- The transition-product factors through the transition-count matrix: each `a → b` transition
contributes `trans a b` exactly `transCount xs a b` times. -/
private theorem transProd_eq_prod_pow_transCount {n : ℕ} (xs : Fin (n + 1) → Fin k) :
    (∏ i : Fin n, M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i))) =
      ∏ ab : Fin k × Fin k, (M.trans ab.1 ab.2) ^ transCount (n := n) xs ab.1 ab.2 := by
  classical
  -- Group the product over indices `i : Fin n` by the adjacent-pair key `(xs i, xs (i+1))`.
  let s : Finset (Fin n) := Finset.univ
  let key : Fin n → Fin k × Fin k := fun i => (xs (Fin.castSucc i), xs (Fin.succ i))
  let step : Fin n → ENNReal := fun i => M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i))
  have hfiber :
      (∏ ab : Fin k × Fin k, ∏ i ∈ s with key i = ab, step i) = ∏ i ∈ s, step i :=
    Finset.prod_fiberwise (s := s) (g := key) (f := step)
  -- Rewrite the RHS as a `Fintype` product over `Fin n`.
  have hstep :
      (∏ i : Fin n, step i) = ∏ i ∈ s, step i := by
    simp [s]
  -- Rewrite each fiber product as a power of the constant transition probability.
  have hinner :
      ∀ ab : Fin k × Fin k,
        (∏ i ∈ s with key i = ab, step i) =
          (M.trans ab.1 ab.2) ^ (s.filter (fun i => key i = ab)).card := by
    intro ab
    rcases ab with ⟨a, b⟩
    -- On the fiber `{ i | key i = ab }`, the factor `step i` is constant.
    have hconst :
        (∏ i ∈ s with key i = (a, b), step i) =
          ∏ _i ∈ s.filter (fun i => key i = (a, b)), M.trans a b := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hkey : key i = (a, b) := (Finset.mem_filter.1 hi).2
      have hab : xs (Fin.castSucc i) = a ∧ xs (Fin.succ i) = b := by
        simpa [key] using hkey
      simp [step, hab.1, hab.2]
    -- Now use `prod_const` to turn the constant product into a power.
    calc
      (∏ i ∈ s with key i = (a, b), step i)
          = ∏ _i ∈ s.filter (fun i => key i = (a, b)), M.trans a b := hconst
      _ = (M.trans a b) ^ (s.filter (fun i => key i = (a, b))).card := by
            exact Finset.prod_const (s := s.filter (fun i => key i = (a, b))) (b := M.trans a b)
  -- Replace the fiber-card with `transCount`, and assemble.
  calc
    (∏ i : Fin n, M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i)))
        = ∏ i ∈ s, step i := by simpa [step] using hstep.symm
    _ = ∏ ab : Fin k × Fin k, ∏ i ∈ s with key i = ab, step i := by
          simp [hfiber]
    _ = ∏ ab : Fin k × Fin k, (M.trans ab.1 ab.2) ^ (s.filter (fun i => key i = ab)).card := by
          -- Apply `hinner` pointwise under the (finite) product.
          exact Fintype.prod_congr _ _ hinner
    _ = ∏ ab : Fin k × Fin k, (M.trans ab.1 ab.2) ^ transCount (n := n) xs ab.1 ab.2 := by
          refine Fintype.prod_congr _ _ ?_
          intro ab
          -- `key i = (a,b)` is the same predicate as used by `transCount`.
          have :
              (s.filter (fun i => key i = ab)).card = transCount (n := n) xs ab.1 ab.2 := by
            -- Rewrite the fiber predicate `key i = (a,b)` into a conjunction on the two coordinates.
            have hfilter :
                s.filter (fun i : Fin n => key i = ab) =
                  s.filter (fun i : Fin n => xs (Fin.castSucc i) = ab.1 ∧ xs (Fin.succ i) = ab.2) := by
              ext i
              simp [s, key, Prod.ext_iff]
            -- `transCount` is defined as the cardinality of the conjunction filter.
            simp [transCount, s, hfilter]
          simp [this]

/-- Adapter lemma: the recursive `prefixAux` along `List.ofFn` is exactly the product of
transition probabilities along adjacent pairs in the trajectory. -/
private theorem prefixAux_ofFn_tail {n : ℕ} (xs : Fin (n + 1) → Fin k) :
    M.prefixAux (xs 0) (List.ofFn (fun i : Fin n => xs i.succ)) =
      ∏ i : Fin n, M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i)) := by
  classical
  induction n with
  | zero =>
      -- No transitions.
      simp [MarkovChain.prefixAux]
  | succ n ih =>
      -- Shift the trajectory by one step.
      let ys : Fin (n + 1) → Fin k := fun i => xs i.succ
      have hcons :
          List.ofFn (fun i : Fin (n + 1) => xs i.succ) =
            xs 1 :: List.ofFn (fun i : Fin n => xs i.succ.succ) := by
        simp [List.ofFn_succ]
      have ih' :
          M.prefixAux (ys 0) (List.ofFn (fun i : Fin n => ys i.succ)) =
            ∏ i : Fin n, M.trans (ys (Fin.castSucc i)) (ys (Fin.succ i)) := by
        -- Apply IH to the shifted trajectory.
        simpa [ys] using ih (xs := ys)
      have hprod :
          (∏ i : Fin (n + 1), M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i))) =
            M.trans (xs 0) (xs 1) * ∏ i : Fin n, M.trans (ys (Fin.castSucc i)) (ys (Fin.succ i)) := by
        -- Split the product into the first transition and the rest.
        simpa [ys, Fin.castSucc_succ, mul_assoc] using
          (Fin.prod_univ_succ (n := n)
            (f := fun i : Fin (n + 1) => M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i))))
      -- Unfold `prefixAux` for the tail list and use IH + the product split.
      calc
        M.prefixAux (xs 0) (List.ofFn (fun i : Fin (n + 1) => xs i.succ))
            = M.trans (xs 0) (xs 1) *
                M.prefixAux (xs 1) (List.ofFn (fun i : Fin n => xs i.succ.succ)) := by
                  simp [MarkovChain.prefixAux]
        _ = M.trans (xs 0) (xs 1) * ∏ i : Fin n, M.trans (ys (Fin.castSucc i)) (ys (Fin.succ i)) := by
              -- Rewrite the recursive call using IH on the shifted trajectory.
              -- The tail list `fun i => xs i.succ.succ` is definitional equal to `fun i => ys i.succ`.
              have hrec :
                  M.prefixAux (xs 1) (List.ofFn (fun i : Fin n => xs i.succ.succ)) =
                    ∏ i : Fin n, M.trans (ys (Fin.castSucc i)) (ys (Fin.succ i)) := by
                simpa [ys] using ih'
              simp [hrec]
        _ = ∏ i : Fin (n + 1), M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i)) := by
              exact hprod.symm

/-- Adapter lemma: the Markov-chain prefix measure on `List.ofFn xs` matches the usual product form
`init(start) * ∏ transitions`. -/
private theorem prefixMeasure_ofFn {n : ℕ} (xs : Fin (n + 1) → Fin k) :
    M.prefixMeasure (List.ofFn xs) =
      M.init (xs 0) * ∏ i : Fin n, M.trans (xs (Fin.castSucc i)) (xs (Fin.succ i)) := by
  classical
  have hcons : List.ofFn xs = xs 0 :: List.ofFn (fun i : Fin n => xs i.succ) := by
    simp [List.ofFn_succ]
  -- Unfold the prefix measure/probability and use `prefixAux_ofFn_tail`.
  simp [MarkovChain.prefixMeasure, MarkovChain.prefixProb, prefixAux_ofFn_tail (M := M) (xs := xs)]

/-- The probability of a finite trajectory factors through `(start, transCount)` under a fixed
Markov chain. -/
  theorem prefixMeasure_markovExchangeable :
      MarkovExchangeablePrefixMeasure (k := k) M.prefixMeasure := by
  classical
  intro n xs₁ xs₂ he
  -- Extract start equality and transition-count equality.
  have hstart : xs₁ 0 = xs₂ 0 := by
    simpa [evidenceOf] using congrArg MarkovEvidence.start he
  have htrans : ∀ a b : Fin k, transCount (n := n) xs₁ a b = transCount (n := n) xs₂ a b := by
    intro a b
    simpa [evidenceOf] using congrArg (fun e => e.trans a b) he
  -- Conclude by rewriting both sides into the product-of-powers normal form.
  calc
    M.prefixMeasure (List.ofFn xs₁)
        = M.init (xs₁ 0) * ∏ i : Fin n, M.trans (xs₁ (Fin.castSucc i)) (xs₁ (Fin.succ i)) :=
          prefixMeasure_ofFn (M := M) (xs := xs₁)
    _ = M.init (xs₁ 0) * ∏ ab : Fin k × Fin k, (M.trans ab.1 ab.2) ^ transCount (n := n) xs₁ ab.1 ab.2 := by
          -- Rewrite the transition product by grouping equal adjacent pairs.
          rw [transProd_eq_prod_pow_transCount (M := M) (xs := xs₁)]
    _ = M.init (xs₂ 0) * ∏ ab : Fin k × Fin k, (M.trans ab.1 ab.2) ^ transCount (n := n) xs₂ ab.1 ab.2 := by
          -- Replace the start symbol and all transition counts.
          simp [hstart, htrans]
    _ = M.init (xs₂ 0) * ∏ i : Fin n, M.trans (xs₂ (Fin.castSucc i)) (xs₂ (Fin.succ i)) := by
          -- Undo the grouping on `xs₂`.
          rw [transProd_eq_prod_pow_transCount (M := M) (xs := xs₂)]
    _ = M.prefixMeasure (List.ofFn xs₂) := (prefixMeasure_ofFn (M := M) (xs := xs₂)).symm

  /-- Domain-test corollary: the 1-step extension probabilities of a fixed Markov chain factor
  through the transition-count evidence state (`TransCounts.summary`) of the history. -/
  theorem prefixMeasure_append_singleton_eq_of_same_summary_list
      (xs ys : List (Fin k)) (hlen : xs.length = ys.length) (hx : 0 < xs.length)
      (hstart : xs.get ⟨0, hx⟩ = ys.get ⟨0, by simpa [hlen] using hx⟩)
      (hsum : TransCounts.summary (k := k) xs = TransCounts.summary (k := k) ys)
      (x : Fin k) :
      M.prefixMeasure (xs ++ [x]) = M.prefixMeasure (ys ++ [x]) := by
    exact
      Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge.mu_append_singleton_eq_of_same_summary_list
        (k := k) (μ := M.prefixMeasure) (hμ := prefixMeasure_markovExchangeable (M := M))
        (xs := xs) (ys := ys) (hlen := hlen) (hx := hx) (hstart := hstart) (hsum := hsum) (x := x)

end MarkovChain

/-! ## Mixtures preserve Markov exchangeability -/

namespace MarkovExchangeabilityBridge

open FiniteAlphabet

variable {ι : Type*} {w : ι → ENNReal} {ν : ι → PrefixMeasure (Fin k)}

theorem markovExchangeable_xiPrefixMeasure (hw : (∑' i : ι, w i) = 1)
    (hν : ∀ i : ι, MarkovExchangeablePrefixMeasure (k := k) (ν i)) :
    MarkovExchangeablePrefixMeasure (k := k) (xiPrefixMeasure ν w hw) := by
  classical
  intro n xs₁ xs₂ he
  -- Expand the mixture and push the `MarkovExchangeablePrefixMeasure` hypothesis inside the `tsum`.
  change
      FiniteAlphabet.xiFun (fun i : ι => (ν i).toSemimeasure) w (List.ofFn xs₁) =
        FiniteAlphabet.xiFun (fun i : ι => (ν i).toSemimeasure) w (List.ofFn xs₂)
  unfold FiniteAlphabet.xiFun
  refine tsum_congr ?_
  intro i
  have hi : (ν i) (List.ofFn xs₁) = (ν i) (List.ofFn xs₂) := hν i n xs₁ xs₂ he
  -- Push the pointwise equality under multiplication, and let `simp` unfold `toSemimeasure`.
  simpa [PrefixMeasure.toSemimeasure] using congrArg (fun t => w i * t) hi

end MarkovExchangeabilityBridge

end MarkovDeFinetti

end Mettapedia.Logic
