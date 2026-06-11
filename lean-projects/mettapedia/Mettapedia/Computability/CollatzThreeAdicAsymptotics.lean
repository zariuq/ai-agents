import Mathlib.Data.Nat.Choose.Basic
import Mettapedia.Computability.CollatzThreeAdicPaths
import Mettapedia.Computability.CollatzThreeAdicExact

/-!
# Balanced-regime asymptotic targets for exact 3-adic Collatz counting

This file does not prove the balanced lower bound yet. It names the exact public
objects that the lower-bound line is trying to control:

* the balanced `(n,k)` regime,
* the scaled Lemma 4.1 upper-model quantity,
* the "polynomially tight" lower-bound target.

The point is to keep the asymptotic target Tim-free and grounded directly in the
exact 3-adic counter from `CollatzThreeAdic`.
-/

namespace CollatzThreeAdic

/-- Balanced regime around `k / n ≈ 1 / 2`. -/
def balancedHalf (n k : Nat) : Prop :=
  49 * n <= 100 * k ∧ 100 * k <= 51 * n

/-- The scaled exact count that removes the manuscript's `1/2 * 3^(k-1)` upper
bound factor. For `k > 0`, the inequality

`scaledExactCount n k <= choose n k`

is exactly the scaled form of the usual Lemma 4.1-style upper model. -/
def scaledExactCount (n k : Nat) : Nat :=
  if k = 0 then
    0
  else
    2 * 3 ^ (k - 1) * totalCount n k

/-- Polynomial slack factor in `n`, used to express the "tight up to
subexponential loss" target in the balanced regime. -/
def polynomialSlack (d n : Nat) : Nat :=
  (n + 1) ^ d

/-- Exponential slack factor `2^(ceil(etaNum * n / etaDen))`, used for weaker
explicit balanced lower-bound targets. -/
def exponentialSlack (etaNum etaDen n : Nat) : Nat :=
  2 ^ ((etaNum * n + etaDen - 1) / etaDen)

/-- The scaled factor relating `totalCount n k` to the Lemma 4.1-style upper
model. For `k = 0` we use `1` so the associated lower-bound surface stays total
without introducing division by `0`. -/
def scaledCountFactor (k : Nat) : Nat :=
  if k = 0 then 1 else 2 * 3 ^ (k - 1)

/-- Lower-bound surface extracted from a polynomial tightness statement. -/
def tightnessLowerBound (d n k : Nat) : Nat :=
  Nat.choose n k / (scaledCountFactor k * polynomialSlack d n)

/-- Lower-bound surface extracted from an explicit rational-exponential balanced
tightness statement. -/
def exponentialTightnessLowerBound (etaNum etaDen n k : Nat) : Nat :=
  Nat.choose n k / (scaledCountFactor k * exponentialSlack etaNum etaDen n)

/-- Public lower-bound target: the exact 3-adic count is within a polynomial
factor of the scaled upper model throughout the balanced regime. -/
def balancedPolynomialTightness : Prop :=
  ∃ N d : Nat,
    ∀ n k,
      N ≤ n →
      balancedHalf n k →
      Nat.choose n k ≤ scaledExactCount n k * polynomialSlack d n

/-- Public weaker balanced target: the exact 3-adic count is within an explicit
fixed exponential slack factor of the scaled upper model. -/
def balancedExponentialTightness (etaNum etaDen : Nat) : Prop :=
  0 < etaDen ∧
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
        Nat.choose n k ≤ scaledExactCount n k * exponentialSlack etaNum etaDen n

/-- Public coefficient-form target: on balanced rows, the exact top
zero-budget admissible-gap coefficient already dominates the explicit
exponential lower-bound surface. This isolates the local-cylinder combinatorial
slice without going through the full cumulative total. -/
def balancedAdmissibleGapCoefficientLowerBound (etaNum etaDen : Nat) : Prop :=
  0 < etaDen ∧
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤
            admissibleGapZeroCount n k (n - k)

/-- Public exact-growth target: the intrinsic exact growth-product floor
already dominates the explicit exponential lower-bound surface throughout the
balanced regime. This packages the remaining lower-bound problem into the exact
sequence `exactStageGrowthLower`. -/
def balancedExactGrowthLowerBound (etaNum etaDen : Nat) : Prop :=
  0 < etaDen ∧
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤ exactGrowthLowerProduct n k

/-- Public ratio-based target: in the balanced regime, there is an explicit
cross-multiplied stagewise ratio witness whose telescoping product already
dominates the exponential lower-bound surface. This is the sharper replacement
for floored growth products when stagewise floor factors collapse to `0`. -/
def balancedExactStageMassRatioLowerBound (etaNum etaDen : Nat) : Prop :=
  0 < etaDen ∧
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          ∃ num den : Nat → Nat,
            0 < growthProduct den k ∧
            exponentialTightnessLowerBound etaNum etaDen n k * growthProduct den k ≤
              growthProduct num k ∧
            ∀ placed, placed < k →
              num placed * exactStageMass (exactStageAt n k placed) ≤
                den placed * exactStageMass (exactStageAt n k (placed + 1))

theorem tightnessLowerBound_le_totalCount_of_choose_bound
    {d n k : Nat}
    (hchoose : Nat.choose n k ≤ scaledExactCount n k * polynomialSlack d n) :
    tightnessLowerBound d n k ≤ totalCount n k := by
  unfold tightnessLowerBound scaledCountFactor
  by_cases hk : k = 0
  · have hFalse : False := by
      simp [scaledExactCount, hk] at hchoose
    exact False.elim hFalse
  · have hden :
        0 < (2 * 3 ^ (k - 1)) * polynomialSlack d n := by
      have hpow : 0 < 3 ^ (k - 1) := Nat.pow_pos (by decide : 0 < 3)
      have hpoly : 0 < polynomialSlack d n := by
        unfold polynomialSlack
        exact Nat.pow_pos (Nat.succ_pos n)
      exact Nat.mul_pos (Nat.mul_pos (by decide) hpow) hpoly
    have hchoose' :
        Nat.choose n k ≤ totalCount n k * ((2 * 3 ^ (k - 1)) * polynomialSlack d n) := by
      simpa [scaledExactCount, hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hchoose
    have hchoose'' :
        Nat.choose n k ≤ ((2 * 3 ^ (k - 1)) * polynomialSlack d n) * totalCount n k := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hchoose'
    simpa [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.div_le_of_le_mul hchoose'' :
        Nat.choose n k / ((2 * 3 ^ (k - 1)) * polynomialSlack d n) ≤ totalCount n k)

theorem balancedPolynomialTightness_implies_eventual_tightnessLowerBound
    (htight : balancedPolynomialTightness) :
    ∃ N d : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
        tightnessLowerBound d n k ≤ totalCount n k := by
  rcases htight with ⟨N, d, hN⟩
  refine ⟨N, d, ?_⟩
  intro n k hn hbal
  exact tightnessLowerBound_le_totalCount_of_choose_bound (hN n k hn hbal)

theorem exponentialTightnessLowerBound_le_totalCount_of_choose_bound
    {etaNum etaDen n k : Nat}
    (hchoose : Nat.choose n k ≤ scaledExactCount n k * exponentialSlack etaNum etaDen n) :
    exponentialTightnessLowerBound etaNum etaDen n k ≤ totalCount n k := by
  unfold exponentialTightnessLowerBound scaledCountFactor
  by_cases hk : k = 0
  · have hFalse : False := by
      simp [scaledExactCount, hk] at hchoose
    exact False.elim hFalse
  · have hden :
        0 < (2 * 3 ^ (k - 1)) * exponentialSlack etaNum etaDen n := by
      have hpow : 0 < 3 ^ (k - 1) := Nat.pow_pos (by decide : 0 < 3)
      have hexp : 0 < exponentialSlack etaNum etaDen n := by
        unfold exponentialSlack
        exact Nat.pow_pos (by decide : 0 < 2)
      exact Nat.mul_pos (Nat.mul_pos (by decide) hpow) hexp
    have hchoose' :
        Nat.choose n k ≤ totalCount n k * ((2 * 3 ^ (k - 1)) * exponentialSlack etaNum etaDen n) := by
      simpa [scaledExactCount, hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hchoose
    have hchoose'' :
        Nat.choose n k ≤ ((2 * 3 ^ (k - 1)) * exponentialSlack etaNum etaDen n) * totalCount n k := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hchoose'
    simpa [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.div_le_of_le_mul hchoose'' :
        Nat.choose n k / ((2 * 3 ^ (k - 1)) * exponentialSlack etaNum etaDen n) ≤ totalCount n k)

theorem balancedExponentialTightness_implies_eventual_exponentialTightnessLowerBound
    {etaNum etaDen : Nat}
    (htight : balancedExponentialTightness etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
        exponentialTightnessLowerBound etaNum etaDen n k ≤ totalCount n k := by
  rcases htight with ⟨_hetaDen, N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  exact exponentialTightnessLowerBound_le_totalCount_of_choose_bound (hN n k hn hbal)

theorem balancedAdmissibleGapCoefficientLowerBound_implies_eventual_totalCountLower
    {etaNum etaDen : Nat}
    (hcoeff : balancedAdmissibleGapCoefficientLowerBound etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤ totalCount n k := by
  rcases hcoeff with ⟨_hetaDen, N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  exact le_trans (hN n k hn hbal) (admissibleGapZeroCount_le_totalCount n k (n - k))

theorem balancedAdmissibleGapCoefficientLowerBound_iff_eventual_finalSemanticsGapPrefixesLower
    {etaNum etaDen : Nat} :
    balancedAdmissibleGapCoefficientLowerBound etaNum etaDen ↔
      0 < etaDen ∧
        ∃ N : Nat,
          ∀ n k,
            N ≤ n →
            balancedHalf n k →
              exponentialTightnessLowerBound etaNum etaDen n k ≤
                (finalSemanticsGapPrefixes n k (n - k)).length := by
  constructor
  · rintro ⟨hetaDen, N, hN⟩
    refine ⟨hetaDen, N, ?_⟩
    intro n k hn hbal
    rw [← admissibleGapZeroCount_eq_length_finalSemanticsGapPrefixes]
    exact hN n k hn hbal
  · rintro ⟨hetaDen, N, hN⟩
    refine ⟨hetaDen, N, ?_⟩
    intro n k hn hbal
    rw [admissibleGapZeroCount_eq_length_finalSemanticsGapPrefixes]
    exact hN n k hn hbal

theorem balancedExactGrowthLowerBound_implies_eventual_exactStageMassLower
    {etaNum etaDen : Nat}
    (hgrowth : balancedExactGrowthLowerBound etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤
            exactStageMass (exactStageAt n k k) := by
  rcases hgrowth with ⟨_hetaDen, N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  exact le_trans (hN n k hn hbal) (exactGrowthLowerProduct_le_exactStageMass_exactStageAt n k)

theorem balancedExactGrowthLowerBound_implies_eventual_stageMass_stageAtLower
    {etaNum etaDen : Nat}
    (hgrowth : balancedExactGrowthLowerBound etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤
            stageMass (stageAt n k k) := by
  rcases hgrowth with ⟨_hetaDen, N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  exact le_trans (hN n k hn hbal) (exactGrowthLowerProduct_le_stageMass_stageAt n k)

theorem balancedExactGrowthLowerBound_implies_eventual_totalCountLower
    {etaNum etaDen : Nat}
    (hgrowth : balancedExactGrowthLowerBound etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤ totalCount n k := by
  rcases balancedExactGrowthLowerBound_implies_eventual_stageMass_stageAtLower hgrowth with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  rw [totalCount_eq_stageMass_stageAt]
  exact hN n k hn hbal

theorem balancedExactGrowthLowerBound_implies_balancedExactStageMassRatioLowerBound
    {etaNum etaDen : Nat}
    (hgrowth : balancedExactGrowthLowerBound etaNum etaDen) :
    balancedExactStageMassRatioLowerBound etaNum etaDen := by
  rcases hgrowth with ⟨hetaDen, N, hN⟩
  refine ⟨hetaDen, N, ?_⟩
  intro n k hn hbal
  have honesAux : ∀ t : Nat, growthProduct (fun _ => 1) t = 1 := by
    intro t
    induction t with
    | zero => simp [growthProduct]
    | succ t ih => simp [growthProduct, ih]
  have hones : growthProduct (fun _ => 1) k = 1 := honesAux k
  refine ⟨exactStageGrowthLower n k, fun _ => 1, ?_, ?_, ?_⟩
  · simp [hones]
  · simpa [exactGrowthLowerProduct, hones] using hN n k hn hbal
  · intro placed hplaced
    simpa [exactStageGrowthLower, Nat.one_mul] using
      exactStageGrowthLower_mul_exactStageMass_exactStageAt_le_succ n k placed

theorem exponentialTightnessLowerBound_le_exactStageMass_of_stageMass_ratio
    {etaNum etaDen n k : Nat} (num den : Nat → Nat)
    (hden : 0 < growthProduct den k)
    (hprod : exponentialTightnessLowerBound etaNum etaDen n k * growthProduct den k ≤ growthProduct num k)
    (hratio : ∀ placed, placed < k →
      num placed * exactStageMass (exactStageAt n k placed) ≤
        den placed * exactStageMass (exactStageAt n k (placed + 1))) :
    exponentialTightnessLowerBound etaNum etaDen n k ≤ exactStageMass (exactStageAt n k k) := by
  have hratioProd :
      growthProduct num k ≤ growthProduct den k * exactStageMass (exactStageAt n k k) :=
    growthProduct_num_le_growthProduct_den_mul_exactStageMass_of_stageMass_ratio n k num den hratio
  have hmul :
      exponentialTightnessLowerBound etaNum etaDen n k * growthProduct den k ≤
        exactStageMass (exactStageAt n k k) * growthProduct den k := by
    exact le_trans hprod (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hratioProd)
  exact Nat.le_of_mul_le_mul_right hmul hden

theorem exponentialTightnessLowerBound_le_stageMass_stageAt_of_stageMass_ratio
    {etaNum etaDen n k : Nat} (num den : Nat → Nat)
    (hden : 0 < growthProduct den k)
    (hprod : exponentialTightnessLowerBound etaNum etaDen n k * growthProduct den k ≤ growthProduct num k)
    (hratio : ∀ placed, placed < k →
      num placed * exactStageMass (exactStageAt n k placed) ≤
        den placed * exactStageMass (exactStageAt n k (placed + 1))) :
    exponentialTightnessLowerBound etaNum etaDen n k ≤ stageMass (stageAt n k k) := by
  rw [← exactStageMass_exactStageAt_eq_stageMass_stageAt]
  exact exponentialTightnessLowerBound_le_exactStageMass_of_stageMass_ratio num den hden hprod hratio

theorem balancedExactStageMassRatioLowerBound_implies_eventual_exactStageMassLower
    {etaNum etaDen : Nat}
    (hratio : balancedExactStageMassRatioLowerBound etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤
            exactStageMass (exactStageAt n k k) := by
  rcases hratio with ⟨_hetaDen, N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  rcases hN n k hn hbal with ⟨num, den, hden, hprod, hstep⟩
  exact exponentialTightnessLowerBound_le_exactStageMass_of_stageMass_ratio num den hden hprod hstep

theorem balancedExactStageMassRatioLowerBound_implies_eventual_stageMass_stageAtLower
    {etaNum etaDen : Nat}
    (hratio : balancedExactStageMassRatioLowerBound etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤
            stageMass (stageAt n k k) := by
  rcases hratio with ⟨_hetaDen, N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  rcases hN n k hn hbal with ⟨num, den, hden, hprod, hstep⟩
  exact exponentialTightnessLowerBound_le_stageMass_stageAt_of_stageMass_ratio
    num den hden hprod hstep

theorem balancedExactStageMassRatioLowerBound_implies_eventual_totalCountLower
    {etaNum etaDen : Nat}
    (hratio : balancedExactStageMassRatioLowerBound etaNum etaDen) :
    ∃ N : Nat,
      ∀ n k,
        N ≤ n →
        balancedHalf n k →
          exponentialTightnessLowerBound etaNum etaDen n k ≤ totalCount n k := by
  rcases balancedExactStageMassRatioLowerBound_implies_eventual_stageMass_stageAtLower hratio with
      ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n k hn hbal
  rw [totalCount_eq_stageMass_stageAt]
  exact hN n k hn hbal

end CollatzThreeAdic
