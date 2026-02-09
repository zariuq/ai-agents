import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open BigOperators

namespace Mettapedia.Logic

/-! ## Finite L1 pushforward bound

This is a purely finite combinatorial inequality: pushing forward two
distributions along a function cannot increase the L1 distance.
-/

lemma l1_pushforward_le
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [DecidableEq Γ]
    (μ ν : Ω → ℝ) (f : Ω → Γ) :
    (∑ γ, abs ((∑ ω, if f ω = γ then μ ω else 0) -
              (∑ ω, if f ω = γ then ν ω else 0)))
      ≤ ∑ ω, abs (μ ω - ν ω) := by
  classical
  -- Triangle inequality inside each fiber.
  have hγ :
      ∀ γ : Γ,
        abs ((∑ ω, if f ω = γ then μ ω else 0) -
            (∑ ω, if f ω = γ then ν ω else 0))
          ≤ ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
    intro γ
    have hdiff :
        (∑ ω, if f ω = γ then (μ ω - ν ω) else 0) =
          (∑ ω, if f ω = γ then μ ω else 0) -
            (∑ ω, if f ω = γ then ν ω else 0) := by
      have hsub :=
        (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset Ω))
          (f := fun ω => if f ω = γ then μ ω else 0)
          (g := fun ω => if f ω = γ then ν ω else 0))
      have hsub' :
          ∑ ω, ((if f ω = γ then μ ω else 0) - (if f ω = γ then ν ω else 0)) =
            ∑ ω, if f ω = γ then (μ ω - ν ω) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro ω _
        by_cases hω : f ω = γ
        · simp [hω, sub_eq_add_neg]
        · simp [hω]
      exact (hsub'.symm.trans hsub)
    have h :=
      (Finset.abs_sum_le_sum_abs
        (s := (Finset.univ : Finset Ω))
        (f := fun ω => if f ω = γ then (μ ω - ν ω) else 0))
    have hrewrite :
        (∑ ω, abs (if f ω = γ then (μ ω - ν ω) else 0)) =
          ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro ω _
      by_cases hω : f ω = γ
      · simp [hω]
      · simp [hω]
    have h' : abs (∑ ω, if f ω = γ then (μ ω - ν ω) else 0) ≤
        ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
      simpa [hrewrite] using h
    simpa [hdiff] using h'

  -- Sum inequality over all γ (finite induction).
  have hsum_le :
      (∑ γ, abs ((∑ ω, if f ω = γ then μ ω else 0) -
              (∑ ω, if f ω = γ then ν ω else 0)))
        ≤ ∑ γ, ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := by
    classical
    refine Finset.induction_on (s := (Finset.univ : Finset Γ)) ?h0 ?hstep
    · simp
    · intro γ s hγs ih
      have hγ' := hγ γ
      have hsum :=
        add_le_add hγ' ih
      -- expand sums over insert
      simpa [Finset.sum_insert, hγs, add_comm, add_left_comm, add_assoc] using hsum

  -- Swap sums.
  have hswap :
      (∑ γ, ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0) =
        ∑ ω, ∑ γ, if f ω = γ then abs (μ ω - ν ω) else 0 := by
    classical
    simpa using
      (Finset.sum_comm
        (s := (Finset.univ : Finset Γ))
        (t := (Finset.univ : Finset Ω))
        (f := fun γ ω => if f ω = γ then abs (μ ω - ν ω) else 0))

  -- Finish by computing the inner γ-sum.
  calc
    (∑ γ, abs ((∑ ω, if f ω = γ then μ ω else 0) -
              (∑ ω, if f ω = γ then ν ω else 0)))
        ≤ ∑ γ, ∑ ω, if f ω = γ then abs (μ ω - ν ω) else 0 := hsum_le
    _ = ∑ ω, ∑ γ, if f ω = γ then abs (μ ω - ν ω) else 0 := hswap
    _ = ∑ ω, abs (μ ω - ν ω) := by
        refine Finset.sum_congr rfl ?_
        intro ω _
        have :
            (∑ γ, if f ω = γ then abs (μ ω - ν ω) else 0) =
              abs (μ ω - ν ω) := by
          classical
          simp
        simp

end Mettapedia.Logic

/-! ## IID vs injective sampling (bound stub)

We will use a finite total-variation bound between uniform iid maps and uniform
injective maps. The concrete bound is a standard collision estimate; to keep
the main proof unblocked we expose it as a lemma with a `sorry` to fill later.
-/

namespace Mettapedia.Logic

/-- Pair-collision mass bound for uniform maps `Fin (n+1) → Fin R`. -/
private lemma pair_mass_le_inv
    (R n : ℕ) (hR : 0 < R)
    (i j0 : Fin (n + 1)) (hij : i ≠ j0) :
    (∑ f : Fin (n + 1) → Fin R,
      if f i = f j0 then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0)
      ≤ (1 : ℝ) / (R : ℝ) := by
  classical
  let S : Finset (Fin (n + 1) → Fin R) :=
    (Finset.univ : Finset (Fin (n + 1) → Fin R)).filter (fun f => f i = f j0)
  let c : ℝ := ((1 : ℝ) / (R : ℝ) ^ (n + 1))
  change (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0) ≤ (1 : ℝ) / (R : ℝ)
  have hsum_card :
      (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0) = (S.card : ℝ) * c := by
    have hcount :
        (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then (1 : ℝ) else 0) = (S.card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [S]
    calc
      (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0)
        = c * (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then (1 : ℝ) else 0) := by
            refine Eq.symm ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro f _
            by_cases h : f i = f j0
            · simp [h, c]
            · simp [h, c]
      _ = c * (S.card : ℝ) := by rw [hcount]
      _ = (S.card : ℝ) * c := by ring
  have hcard_le : S.card ≤ Fintype.card (Fin n → Fin R) := by
    refine Finset.card_le_card_of_injOn (f := fun f : Fin (n + 1) → Fin R => j0.removeNth f) ?hmaps ?hinj
    · intro f hf
      simp
    · intro f hf g hg hfg
      apply funext
      intro x
      by_cases hx : x = j0
      · subst x
        have hfi_eq_fj : f i = f j0 := (Finset.mem_filter.mp hf).2
        have hgi_eq_gj : g i = g j0 := (Finset.mem_filter.mp hg).2
        have hi_eq : f i = g i := by
          have hi_mem : i ∈ Set.range j0.succAbove := by
            have : i ∈ ({j0}ᶜ : Set (Fin (n + 1))) := by
              simpa [Set.mem_compl] using hij
            simpa [Fin.range_succAbove] using this
          rcases hi_mem with ⟨t, rfl⟩
          have hfg' := congrArg (fun h : Fin n → Fin R => h t) hfg
          simpa [Fin.removeNth] using hfg'
        exact (hfi_eq_fj.symm.trans hi_eq).trans hgi_eq_gj
      · have hx_mem : x ∈ Set.range j0.succAbove := by
          have : x ∈ ({j0}ᶜ : Set (Fin (n + 1))) := by
            simpa [Set.mem_compl] using hx
          simpa [Fin.range_succAbove] using this
        rcases hx_mem with ⟨t, rfl⟩
        have hfg' := congrArg (fun h : Fin n → Fin R => h t) hfg
        simpa [Fin.removeNth] using hfg'
  have hcard_pow : Fintype.card (Fin n → Fin R) = R ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hcard_bound : (S.card : ℝ) ≤ (R : ℝ) ^ n := by
    have hnat : S.card ≤ R ^ n := by simpa [hcard_pow] using hcard_le
    exact_mod_cast hnat
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  calc
    (∑ f : Fin (n + 1) → Fin R, if f i = f j0 then c else 0)
      = (S.card : ℝ) * c := hsum_card
    _ ≤ ((R : ℝ) ^ n) * c := by exact mul_le_mul_of_nonneg_right hcard_bound (by positivity)
    _ = (1 : ℝ) / (R : ℝ) := by
      dsimp [c]
      have hpow : (R : ℝ) ^ (n + 1) = (R : ℝ) ^ n * (R : ℝ) := by
        simp [pow_succ, mul_comm]
      rw [hpow]
      field_simp [hRr]

/-- Sum of all ordered pair-collision masses is bounded by `m^2 / R`
for `m = n+1`. -/
private lemma pair_sum_le_sq_inv
    (R n : ℕ) (hR : 0 < R) :
    let c : ℝ := ((1 : ℝ) / (R : ℝ) ^ (n + 1))
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if i = j then (0 : ℝ)
      else (∑ f : Fin (n + 1) → Fin R, if f i = f j then c else 0))
      ≤ ((n + 1 : ℝ) * (n + 1 : ℝ)) / (R : ℝ) := by
  classical
  dsimp
  have hterm :
      ∀ i : Fin (n + 1),
      ∀ j : Fin (n + 1),
      (if i = j then (0 : ℝ)
        else (∑ f : Fin (n + 1) → Fin R,
          if f i = f j then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0))
      ≤ (1 : ℝ) / (R : ℝ) := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
      simpa [one_div] using pair_mass_le_inv R n hR i j hij
  have hsum_le :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        if i = j then (0 : ℝ)
        else (∑ f : Fin (n + 1) → Fin R,
          if f i = f j then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0))
      ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ((1 : ℝ) / (R : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hterm i j
  calc
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if i = j then (0 : ℝ)
      else (∑ f : Fin (n + 1) → Fin R,
        if f i = f j then ((1 : ℝ) / (R : ℝ) ^ (n + 1)) else 0))
      ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ((1 : ℝ) / (R : ℝ)) := hsum_le
    _ = ((n + 1 : ℝ) * (n + 1 : ℝ)) / (R : ℝ) := by
      simp [Finset.sum_const, Fintype.card_fin, mul_comm, mul_left_comm]
      ring

/-- L1 distance between iid and injective distributions (collision bound).
    This is the Diaconis–Freedman finite core estimate. -/
lemma l1_iid_inj_le
    (R m : ℕ) (hR : 0 < R) (hRm : m ≤ R) :
    (∑ f : Fin m → Fin R,
        abs ((1 : ℝ) / (R : ℝ) ^ m -
          (if Function.Injective f then (1 : ℝ) / (R : ℝ) ^ m / (∑ g : Fin m → Fin R,
           if Function.Injective g then (1 : ℝ) / (R : ℝ) ^ m else 0)
           else 0)))
      ≤ (4 : ℝ) * (m : ℝ) * (m : ℝ) / (R : ℝ) := by
  -- TODO: complete by conditioning-on-injective + collision union bound:
  -- 1) `L1 = 2 * Pbad`,
  -- 2) `Pbad ≤ m^2 / R` using ordered pair collisions and `pair_mass_le_inv`,
  -- 3) conclude with slack factor `4`.
  sorry

end Mettapedia.Logic
