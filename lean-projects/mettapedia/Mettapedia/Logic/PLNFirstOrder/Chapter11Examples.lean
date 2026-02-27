import Mettapedia.Logic.PLNFirstOrder.FuzzyITVBridge
import Mettapedia.Logic.PLNIndefiniteTruth

/-!
# Chapter 11 Worked Examples (Canary Theorems)

This module provides theorem-level canaries aligned with the Chapter-11 narrative:

1. A "crooked lottery"-style case where only a minority are near-certain winners.
2. A fuzzy syllogism-style case where composed scores stay in a "many" interval.
3. Explicit non-equivalence witness for the Ch.11 rule-4 shape on an ITV-based path.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Mettapedia.Logic.PLNIndefiniteTruth

/-- Shared ε=0.1 fixture with AFew-like interval `[0.4,0.6]` and strong `PCL=0.9`. -/
def ch11AFewParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.6
  PCL := 0.9
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Shared ε=0.1 fixture with MANY-like interval `[0.4,0.95]`. -/
def ch11ManyParams : FuzzyQuantifierParams where
  ε := 0.1
  LPC := 0.4
  UPC := 0.95
  PCL := 0.4
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- One high-probability witness, one low-probability witness. -/
def oneHighOneLow : Bool → ℝ :=
  fun b => if b then 0.95 else 0.05

/-- Both witnesses high. -/
def bothHigh : Bool → ℝ :=
  fun _ => 0.95

/-- Both witnesses low. -/
def bothLow : Bool → ℝ :=
  fun _ => 0.05

/-- Crooked-lottery canary:
`AFew` holds while strict `ForAll` (via `PCL=0.9`) does not. -/
theorem canary_ch11_crookedLottery_afew_not_forall :
    fuzzyIntervalHolds ch11AFewParams oneHighOneLow ∧
      ¬ fuzzyForAllHolds ch11AFewParams oneHighOneLow := by
  have hfrac : nearOneFraction ch11AFewParams oneHighOneLow = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11AFewParams (oneHighOneLow u)) =
          (fun u => u = true) := by
      funext u
      cases u <;> simp [nearOne, oneHighOneLow, ch11AFewParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  constructor
  · unfold fuzzyIntervalHolds
    rw [hfrac]
    norm_num [ch11AFewParams]
  · unfold fuzzyForAllHolds
    rw [hfrac]
    norm_num [ch11AFewParams]

/-- Fuzzy-syllogism canary:
with "many women are beautiful" and "almost all beautiful bring happiness"
encoded as near-one fractions `1/2` and `1`, the composed score remains "many". -/
theorem canary_ch11_fuzzySyllogism_many :
    ch11ManyParams.LPC ≤
        nearOneFraction ch11ManyParams oneHighOneLow *
          nearOneFraction ch11ManyParams bothHigh ∧
      nearOneFraction ch11ManyParams oneHighOneLow *
          nearOneFraction ch11ManyParams bothHigh ≤
        ch11ManyParams.UPC := by
  have hWB : nearOneFraction ch11ManyParams oneHighOneLow = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams (oneHighOneLow u)) =
          (fun u => u = true) := by
      funext u
      cases u <;> simp [nearOne, oneHighOneLow, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hBH : nearOneFraction ch11ManyParams bothHigh = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams (bothHigh u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearOne, bothHigh, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  rw [hWB, hBH]
  norm_num [ch11ManyParams]

/-- Positive fixture: all-high profile satisfies strict fuzzy `ForAll` under AFew parameters. -/
theorem canary_ch11_allHigh_forall :
    fuzzyForAllHolds ch11AFewParams bothHigh := by
  have hBH : nearOneFraction ch11AFewParams bothHigh = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11AFewParams (bothHigh u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearOne, bothHigh, ch11AFewParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  unfold fuzzyForAllHolds
  rw [hBH]
  norm_num [ch11AFewParams]

/-- Negative fixture: all-low profile fails fuzzy `ThereExists` under AFew parameters. -/
theorem canary_ch11_allLow_not_thereExists :
    ¬ fuzzyThereExistsHolds ch11AFewParams bothLow := by
  have hBZ : nearZeroFraction ch11AFewParams bothLow = (1 : ℝ) := by
    have hpred :
        (fun u : Bool => nearZero ch11AFewParams (bothLow u)) = (fun _ => True) := by
      funext u
      cases u <;> simp [nearZero, bothLow, ch11AFewParams] <;> norm_num
    unfold nearZeroFraction
    simp [hpred, witnessFraction, witnessCount]
  unfold fuzzyThereExistsHolds
  rw [hBZ]
  norm_num [ch11AFewParams]

/-- ITV fixtures for explicit rule-4 non-equivalence witness. -/
def itvHi : ITV where
  lower := 0.9
  upper := 1
  credibility := 0.8
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def itvLo : ITV where
  lower := 0
  upper := 0.2
  credibility := 0.8
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

def itvG : ITV where
  lower := 0.55
  upper := 0.65
  credibility := 0.9
  lower_le_upper := by norm_num
  lower_in_unit := by norm_num
  upper_in_unit := by norm_num
  credibility_in_unit := by norm_num

/-- ε=0.2 makes "near one" mean `x ≥ 0.8`. -/
def ch11Rule4Params : FuzzyQuantifierParams where
  ε := 0.2
  LPC := 0
  UPC := 1
  PCL := 0
  hε := by norm_num
  hLPC := by norm_num
  hUPC := by norm_num
  hPCL := by norm_num
  hLPC_le_UPC := by norm_num

/-- Profile induced by ITV midpoint strengths. -/
noncomputable def rule4Profile : Bool → ℝ :=
  fun b => (if b then itvHi else itvLo).strength

/-- Concrete ITV-valued finite fixture used by coordinate bridge canaries. -/
def rule4ITVProfile : Bool → ITV :=
  fun b => if b then itvHi else itvLo

/-- Ch.11 Rule-4 non-equivalence witness on an ITV-based path:

`∃x (G ∧ F(x))` score is not equal to `G ∧ ∃x F(x)` score under proxy-threshold
aggregation. -/
theorem canary_ch11_rule4_not_equivalent_itvPath :
    fuzzyExistsScore ch11Rule4Params
      (conjoinProfile itvG.strength rule4Profile)
      ≠
    min itvG.strength (fuzzyExistsScore ch11Rule4Params rule4Profile) := by
  have hLeft :
      fuzzyExistsScore ch11Rule4Params (conjoinProfile itvG.strength rule4Profile) = (0 : ℝ) := by
    unfold fuzzyExistsScore nearOneFraction witnessFraction witnessCount nearOne
    unfold conjoinProfile rule4Profile ch11Rule4Params
    norm_num [ITV.strength, itvG, itvHi, itvLo]
  have hScore :
      fuzzyExistsScore ch11Rule4Params rule4Profile = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11Rule4Params (rule4Profile u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, rule4Profile, ch11Rule4Params, ITV.strength, itvHi, itvLo] <;> norm_num
    unfold fuzzyExistsScore nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hRight :
      min itvG.strength (fuzzyExistsScore ch11Rule4Params rule4Profile) = (1 / 2 : ℝ) := by
    rw [hScore]
    norm_num [ITV.strength, itvG]
  rw [hLeft, hRight]
  norm_num

/-- ITV-coordinate bridge canary:
lower/upper fuzzy-interval truth transfers to strength-profile truth. -/
theorem canary_ch11_itv_strength_interval_of_lower_upper :
    fuzzyIntervalHolds ch11ManyParams (itvLowerProfile rule4ITVProfile) ∧
      fuzzyIntervalHolds ch11ManyParams (itvUpperProfile rule4ITVProfile) ∧
      fuzzyIntervalHolds ch11ManyParams (itvStrengthProfile rule4ITVProfile) := by
  have hLowerFrac : nearOneFraction ch11ManyParams (itvLowerProfile rule4ITVProfile) = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams ((itvLowerProfile rule4ITVProfile) u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, itvLowerProfile, rule4ITVProfile, itvHi, itvLo, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hUpperFrac : nearOneFraction ch11ManyParams (itvUpperProfile rule4ITVProfile) = (1 / 2 : ℝ) := by
    have hpred :
        (fun u : Bool => nearOne ch11ManyParams ((itvUpperProfile rule4ITVProfile) u)) =
          (fun u => u = true) := by
      funext u
      cases u <;>
        simp [nearOne, itvUpperProfile, rule4ITVProfile, itvHi, itvLo, ch11ManyParams] <;> norm_num
    unfold nearOneFraction
    simp [hpred, witnessFraction, witnessCount]
  have hLower : fuzzyIntervalHolds ch11ManyParams (itvLowerProfile rule4ITVProfile) := by
    unfold fuzzyIntervalHolds
    rw [hLowerFrac]
    norm_num [ch11ManyParams]
  have hUpper : fuzzyIntervalHolds ch11ManyParams (itvUpperProfile rule4ITVProfile) := by
    unfold fuzzyIntervalHolds
    rw [hUpperFrac]
    norm_num [ch11ManyParams]
  refine ⟨hLower, hUpper, ?_⟩
  exact fuzzyIntervalHolds_strength_of_lower_upper ch11ManyParams rule4ITVProfile hLower hUpper

end Mettapedia.Logic.PLNFirstOrder
