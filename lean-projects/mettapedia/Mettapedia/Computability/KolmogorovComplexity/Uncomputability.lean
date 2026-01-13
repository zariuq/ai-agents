import Mathlib.Computability.Partrec
import Mathlib.Data.Bool.Basic
import Mettapedia.Computability.HutterComputability
import Mettapedia.Computability.KolmogorovComplexity.Basic

/-!
# (Non)computability of Kolmogorov complexity (Hutter 2005, Theorem 2.13)

Hutter (2005), Chapter 2, Theorem 2.13 states that Kolmogorov complexity is not
"finitely computable" (and discusses co-enumerability).

We formalize the core noncomputability statement for the plain complexity `K(x)`
from `Mettapedia.Computability.KolmogorovComplexity.Basic`.

Proof idea (standard, via incompressible strings):
1. If `K` were computable, we could (partially recursively) search for an incompressible
   string of length `2^n`.
2. A universal algorithm can output this string from an input/program of length `n`
   (up to an additive constant), giving `K(x) ≤ n + c`.
3. Incompressibility gives `K(x) ≥ 2^n - 1`, contradiction for `n = c + 2`.
-/

namespace KolmogorovComplexity

open scoped Classical

open Mettapedia.Computability.Hutter

/-! ## Elementary growth bounds -/

/-- `2^n ≥ n+1` for all `n`. -/
theorem two_pow_ge_succ (n : ℕ) : (2 : ℕ) ^ n ≥ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- `2^(n+1) = 2^n * 2 ≥ (n+1) * 2 = (n+1) + (n+1) ≥ (n+1) + 1`.
      calc
        (2 : ℕ) ^ n.succ = (2 : ℕ) ^ n * 2 := by simp [Nat.pow_succ]
        _ ≥ (n + 1) * 2 := Nat.mul_le_mul_right 2 ih
        _ = (n + 1) + (n + 1) := by simp [mul_two]
        _ ≥ (n + 1) + 1 := Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le n)) (n + 1)

/-- A concrete inequality used to contradict `K(x) ≤ n + c` with `K(x) ≥ 2^n - 1`.

We show `2^(c+2) - 1 > (c+2) + c`.
-/
theorem two_pow_succ_succ_sub_one_gt (c : ℕ) : (2 : ℕ) ^ (c + 2) - 1 > (c + 2) + c := by
  have hc : (2 : ℕ) ^ c ≥ c + 1 := two_pow_ge_succ c
  have hPow : (2 : ℕ) ^ (c + 2) = (2 : ℕ) ^ c * 4 := by
    simp [Nat.pow_add]
  have hLower : (2 : ℕ) ^ (c + 2) ≥ (c + 1) * 4 := by
    have : (2 : ℕ) ^ c * 4 ≥ (c + 1) * 4 := Nat.mul_le_mul_right 4 hc
    simpa [hPow] using this
  have hLin : (c + 1) * 4 - 1 > (c + 2) + c := by
    -- `(c+1)*4 - 1 ≥ 4c+3` and `4c+3 > 2c+2 = (c+2)+c`.
    have h1 : (c + 2) + c = 2 * c + 2 := by
      -- `c+2+c = c+c+2 = 2*c+2`
      simp [two_mul, Nat.add_assoc, Nat.add_comm]
    have h2 : (4 : ℕ) * c + 3 > (2 : ℕ) * c + 2 := by
      -- `2c+2 < 2c+3 ≤ 4c+3`.
      have hlt : (2 : ℕ) * c + 2 < (2 : ℕ) * c + 3 := by
        have hs : ((2 : ℕ) * c + 2).succ = (2 : ℕ) * c + 3 := by
          simp [Nat.succ_eq_add_one, Nat.add_assoc]
        exact lt_of_lt_of_eq (Nat.lt_succ_self ((2 : ℕ) * c + 2)) hs
      have hle : (2 : ℕ) * c + 3 ≤ (4 : ℕ) * c + 3 := by
        have hmul : (2 : ℕ) * c ≤ (4 : ℕ) * c := Nat.mul_le_mul_right c (by decide : (2 : ℕ) ≤ 4)
        exact Nat.add_le_add_right hmul 3
      exact lt_of_lt_of_le hlt hle
    -- Rewrite both sides.
    have h3 : (c + 1) * 4 - 1 = (4 : ℕ) * c + 3 := by
      -- `(c+1)*4 = 4*c + 4`.
      simp [Nat.add_mul, Nat.mul_comm, Nat.add_comm]
    -- combine
    simpa [h1, h3, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2
  have hmono : (2 : ℕ) ^ (c + 2) - 1 ≥ (c + 1) * 4 - 1 := Nat.sub_le_sub_right hLower 1
  have hmono' : (c + 1) * 4 - 1 ≤ (2 : ℕ) ^ (c + 2) - 1 := by simpa using hmono
  exact lt_of_lt_of_le hLin hmono'

/-! ## A computable search step -/

/-- Given `n` and an index `t`, try to decode `t` as a string `x` and return it iff
it witnesses incompressibility at length `2^n`.

This is designed to be used with `Nat.rfindOpt`.
-/
noncomputable def incompressibleCandidate (K : BinString → ℕ) (n t : ℕ) : Option BinString :=
  match Encodable.decode (α := BinString) t with
  | none => none
  | some x =>
      let m := (2 : ℕ) ^ n
      let lenOk : Bool := decide (x.length = m)
      let kOk : Bool := decide (m - 1 ≤ K x)
      cond (lenOk && kOk) (some x) none

/-- If `x` is returned by `incompressibleCandidate`, it has the advertised length and
complexity lower bound. -/
theorem incompressibleCandidate_spec {K : BinString → ℕ} {n t : ℕ} {x : BinString}
    (hx : x ∈ incompressibleCandidate K n t) :
    x.length = (2 : ℕ) ^ n ∧ (2 : ℕ) ^ n - 1 ≤ K x := by
  classical
  unfold incompressibleCandidate at hx
  cases hdec : (Encodable.decode (α := BinString) t) with
  | none =>
      -- `none` cannot contain any witness.
      rw [hdec] at hx
      cases hx
  | some y =>
      -- Reduce the outer `match` by rewriting, without triggering simp rewriting inside `decide`.
      rw [hdec] at hx
      set m : ℕ := (2 : ℕ) ^ n
      have hxEq :
          cond (decide (y.length = m) && decide (m - 1 ≤ K y)) (some y) none = some x := by
        simpa [m] using hx
      cases hb : (decide (y.length = m) && decide (m - 1 ≤ K y)) with
      | false =>
          have hxEq' := hxEq
          rw [hb] at hxEq'
          dsimp [cond] at hxEq'
          cases hxEq'
      | true =>
          have hxEq' := hxEq
          rw [hb] at hxEq'
          dsimp [cond] at hxEq'
          have hxy : y = x := Option.some.inj hxEq'
          subst y
          have hBoth : decide (x.length = m) = true ∧ decide (m - 1 ≤ K x) = true :=
            (Eq.mp (Bool.and_eq_true_eq_eq_true_and_eq_true _ _) (by simpa using hb))
          exact ⟨of_decide_eq_true hBoth.1, of_decide_eq_true hBoth.2⟩

/-- A convenient witness: if `x` has the right length and complexity lower bound, it is
accepted by `incompressibleCandidate` at index `encode x`.
-/
theorem incompressibleCandidate_encode_mem (K : BinString → ℕ) (n : ℕ) (x : BinString)
    (hlen : x.length = (2 : ℕ) ^ n) (hK : (2 : ℕ) ^ n - 1 ≤ K x) :
    x ∈ incompressibleCandidate K n (Encodable.encode x) := by
  classical
  unfold incompressibleCandidate
  -- decode(encode x) = some x
  simp [Encodable.encodek, hlen, hK, cond]

/-- If `K` is computable, then `incompressibleCandidate K` is computable (as a 2-argument function). -/
theorem incompressibleCandidate_computable {K : BinString → ℕ} (hK : Computable K) :
    Computable₂ (incompressibleCandidate K) := by
  classical
  -- Primitive recursive ingredients.
  have hPow : Computable₂ (fun a b : ℕ => a ^ b) := by
    have hPrim : Primrec₂ (fun a b : ℕ => a ^ b) := (Primrec₂.unpaired'.1 Nat.Primrec.pow)
    exact hPrim.to_comp
  have hPow2 : Computable (fun n : ℕ => (2 : ℕ) ^ n) :=
    by simpa using (Computable₂.comp (hf := hPow) (hg := (Computable.const 2))
      (hh := (Computable.id : Computable (fun n : ℕ => n))))
  have hDecEq : Computable₂ (fun a b : ℕ => decide (a = b)) := by
    have hPrim : Primrec₂ (fun a b : ℕ => decide (a = b)) :=
      PrimrecRel.decide (R := fun a b : ℕ => a = b) (hR := (Primrec.eq : PrimrecRel (@Eq ℕ)))
    exact hPrim.to_comp
  have hDecLe : Computable₂ (fun a b : ℕ => decide (a ≤ b)) := by
    have hPrim : Primrec₂ (fun a b : ℕ => decide (a ≤ b)) :=
      PrimrecRel.decide (R := fun a b : ℕ => a ≤ b) (hR := Primrec.nat_le)
    exact hPrim.to_comp
  have hAnd : Computable₂ (fun a b : Bool => a && b) := by
    simpa using (Primrec.and.to_comp : Computable₂ (fun a b : Bool => and a b))

  -- Prove computability on a pair `(n,t)`.
  refine Computable₂.mk ?_
  let α := ℕ × ℕ
  have hDecode : Computable (fun p : α => Encodable.decode (α := BinString) p.2) :=
    (Computable.decode : Computable (Encodable.decode (α := BinString))).comp (Computable.snd : Computable (Prod.snd : α → ℕ))
  have hNone : Computable (fun _ : α => (none : Option BinString)) := Computable.const _

  -- The `some`-branch: given `(n,t)` and decoded `x`, decide the predicate and return `some x` or `none`.
  have hSome : Computable₂ (fun p : α => fun x : BinString =>
      let m := (2 : ℕ) ^ p.1
      let lenOk : Bool := decide (x.length = m)
      let kOk : Bool := decide (m - 1 ≤ K x)
      cond (lenOk && kOk) (some x) none) := by
    -- Work on the uncurried function `((n,t),x)`.
    refine Computable₂.mk ?_
    -- Domain is `α × BinString`.
    let β := BinString
    -- Helper: `m((p,x)) = 2^(p.1)`.
    have hFirst : Computable (fun q : α × β => q.1.1) :=
      (Computable.fst : Computable (Prod.fst : α → ℕ)).comp
        (Computable.fst : Computable (Prod.fst : α × β → α))
    have hm : Computable (fun q : α × β => (2 : ℕ) ^ q.1.1) := hPow2.comp hFirst
    have hlen : Computable (fun q : α × β => q.2.length) :=
      (Computable.list_length : Computable (List.length : BinString → ℕ)).comp (Computable.snd : Computable (Prod.snd : α × β → β))
    have hK' : Computable (fun q : α × β => K q.2) := hK.comp (Computable.snd : Computable (Prod.snd : α × β → β))
    -- lenOk(q) = decide (len(q) = m(q))
    have hLenOk : Computable (fun q : α × β => decide (q.2.length = (2 : ℕ) ^ q.1.1)) :=
      (hDecEq.comp (hlen) (hm))
    -- kOk(q) = decide (m(q) - 1 ≤ K(q))
    have hPred : Computable (fun q : α × β => ((2 : ℕ) ^ q.1.1) - 1) := by
      -- `q ↦ m(q) - 1` is computable by composing with subtraction-by-1.
      -- We use `Nat.pred` via `sub` since it is already primitive recursive.
      have hSub : Computable₂ (fun a b : ℕ => a - b) := by
        have hPrim : Primrec₂ (fun a b : ℕ => a - b) := (Primrec₂.unpaired'.1 Nat.Primrec.sub)
        exact hPrim.to_comp
      have hOne : Computable (fun _q : α × β => (1 : ℕ)) := Computable.const 1
      simpa using (Computable₂.comp (hf := hSub) (hg := hm) (hh := hOne))
    have hKOk : Computable (fun q : α × β => decide (((2 : ℕ) ^ q.1.1) - 1 ≤ K q.2)) :=
      (hDecLe.comp hPred hK')
    have hCond : Computable (fun q : α × β => (decide (q.2.length = (2 : ℕ) ^ q.1.1)) &&
        decide (((2 : ℕ) ^ q.1.1) - 1 ≤ K q.2)) :=
      (hAnd.comp hLenOk hKOk)
    have hSomeX : Computable (fun q : α × β => (some q.2 : Option BinString)) :=
      (Computable.option_some : Computable (@Option.some BinString)).comp (Computable.snd : Computable (Prod.snd : α × β → β))
    have hNoneX : Computable (fun _q : α × β => (none : Option BinString)) := Computable.const _
    -- Finally: if cond then some x else none
    simpa [cond] using (Computable.cond hCond hSomeX hNoneX)

  -- Put the `Option.casesOn` together.
  -- `Option.casesOn (decode t) none (fun x => ...)` equals our `match`.
  refine
      (Computable.option_casesOn (o := fun p : α => Encodable.decode (α := BinString) p.2)
        (f := fun _p : α => (none : Option BinString))
        (g := fun p x =>
          let m := (2 : ℕ) ^ p.1
          let lenOk : Bool := decide (x.length = m)
          let kOk : Bool := decide (m - 1 ≤ K x)
          cond (lenOk && kOk) (some x) (none : Option BinString))
        hDecode hNone hSome).of_eq ?_
  intro p
  unfold incompressibleCandidate
  cases Encodable.decode (α := BinString) p.2 <;> rfl

/-! ## Theorem 2.13 (noncomputability) -/

/-- **Theorem 2.13 (noncomputability, plain `K`)**: `K(x)` is not finitely computable. -/
theorem kolmogorovComplexity_not_finitelyComputable :
    ¬ FinitelyComputable (kolmogorovComplexity : BinString → ℕ) := by
  intro hK
  have hK' : Computable (kolmogorovComplexity : BinString → ℕ) := hK

  -- Build the partial-recursive search `n ↦ rfindOpt (candidate K n)`.
  have hCand : Computable₂ (incompressibleCandidate (kolmogorovComplexity : BinString → ℕ)) :=
    incompressibleCandidate_computable (K := (kolmogorovComplexity : BinString → ℕ)) hK'
  have hSearch : Partrec (fun n : ℕ => Nat.rfindOpt (incompressibleCandidate (kolmogorovComplexity : BinString → ℕ) n)) :=
    Partrec.rfindOpt (f := incompressibleCandidate (kolmogorovComplexity : BinString → ℕ)) hCand

  -- Turn it into an `Algorithm` by feeding the program length.
  let searchAlg : Algorithm := fun p => Nat.rfindOpt (incompressibleCandidate (kolmogorovComplexity : BinString → ℕ) p.length)
  have hSearchAlg : Partrec searchAlg :=
    (hSearch.comp (Computable.list_length : Computable (List.length : BinString → ℕ)))

  -- Universality: the fixed universal algorithm underlying `K` can simulate `searchAlg` with
  -- a fixed prefix overhead.
  let U : Algorithm := Classical.choose exists_optimal_algorithm
  have hU : IsUniversal U := universal_is_universal
  obtain ⟨code, hcode⟩ := hU searchAlg hSearchAlg

  -- Choose `n = code.length + 2`.
  let n : ℕ := code.length + 2
  let p : BinString := List.replicate n false
  have hp_len : p.length = n := by simp [p]

  -- Show the search returns some `x` at this `n`.
  have hExistsIncomp : ∃ x : BinString, x.length = (2 : ℕ) ^ n ∧ kolmogorovComplexity x ≥ (2 : ℕ) ^ n - 1 := by
    -- `most_strings_incompressible` gives `K(x) ≥ m-1` at length `m`.
    simpa using (most_strings_incompressible (n := (2 : ℕ) ^ n) (k := 1) (hk := Nat.succ_pos 0))
  rcases hExistsIncomp with ⟨x0, hx0_len, hx0_K⟩
  have hx0_mem : x0 ∈ incompressibleCandidate (kolmogorovComplexity : BinString → ℕ) n (Encodable.encode x0) := by
    -- `incompressibleCandidate_encode_mem` expects `≤`.
    have hx0_K'' : (2 : ℕ) ^ n - 1 ≤ kolmogorovComplexity x0 := by
      simpa [ge_iff_le] using hx0_K
    exact incompressibleCandidate_encode_mem (K := (kolmogorovComplexity : BinString → ℕ)) n x0 hx0_len hx0_K''
  have hDom : (Nat.rfindOpt (incompressibleCandidate (kolmogorovComplexity : BinString → ℕ) n)).Dom := by
    -- rfindOpt is defined if some index returns `some x`.
    exact (Nat.rfindOpt_dom).2 ⟨Encodable.encode x0, x0, hx0_mem⟩

  let x : BinString := (Nat.rfindOpt (incompressibleCandidate (kolmogorovComplexity : BinString → ℕ) n)).get hDom
  have hx_in : x ∈ Nat.rfindOpt (incompressibleCandidate (kolmogorovComplexity : BinString → ℕ) n) :=
    Part.get_mem hDom

  -- The chosen `x` satisfies incompressibility at length `2^n`.
  have hxSpec : x.length = (2 : ℕ) ^ n ∧ (2 : ℕ) ^ n - 1 ≤ kolmogorovComplexity x := by
    -- rfindOpt_spec gives a witness `t` such that `x ∈ candidate n t`.
    rcases Nat.rfindOpt_spec hx_in with ⟨t, ht⟩
    exact incompressibleCandidate_spec (K := (kolmogorovComplexity : BinString → ℕ)) (n := n) (t := t) ht

  -- `x` is produced by `searchAlg p`, hence by universality also by `U (code ++ p)`.
  have hx_search : x ∈ searchAlg p := by
    -- searchAlg p = rfindOpt (candidate n) and `p.length = n`.
    have : x ∈ Nat.rfindOpt (incompressibleCandidate (kolmogorovComplexity : BinString → ℕ) n) := hx_in
    simpa [searchAlg, hp_len] using this
  have hx_U : x ∈ U (code ++ p) := hcode p x hx_search

  -- Upper bound: `K(x) ≤ |code++p| = n + code.length`.
  have hUpper : kolmogorovComplexity x ≤ (code ++ p).length := by
    -- `K(x)` is `C[U](x)`.
    have hC : C[U](x) ≤ (code ++ p).length := complexity_le_of_program U x (code ++ p) hx_U
    simpa [kolmogorovComplexity] using hC
  have hUpper' : kolmogorovComplexity x ≤ n + code.length := by
    simpa [List.length_append, hp_len, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hUpper

  -- Lower bound from incompressibility.
  have hLower : (2 : ℕ) ^ n - 1 ≤ kolmogorovComplexity x := hxSpec.2

  -- Contradiction: `2^n - 1 > n + code.length` but also `2^n - 1 ≤ K(x) ≤ n + code.length`.
  have hGrow : (2 : ℕ) ^ n - 1 > n + code.length := by
    -- `n = code.length + 2`.
    simpa [n, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (two_pow_succ_succ_sub_one_gt (c := code.length))

  have : (2 : ℕ) ^ n - 1 ≤ n + code.length := le_trans hLower hUpper'
  exact (not_lt_of_ge this) hGrow

end KolmogorovComplexity
