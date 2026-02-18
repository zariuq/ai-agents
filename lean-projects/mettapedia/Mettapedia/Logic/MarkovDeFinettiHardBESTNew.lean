import Mettapedia.Logic.MarkovDeFinettiHardEuler
import Mettapedia.Logic.MarkovDeFinettiHardBESTCore
import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical
import Mettapedia.Logic.MarkovDeFinettiHardCopyPerm
import Mettapedia.Logic.MarkovDeFinettiHardEulerTrails
import Mettapedia.Logic.MarkovDeFinettiHardExcursionBridge

/-!
Active extracted cluster for HardBEST cleanup.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardBEST

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiHardEuler
open Mettapedia.Logic.MarkovDeFinettiHardCopyPerm
open Mettapedia.Logic.MarkovDeFinettiHardEulerTrails
open Mettapedia.Logic.MarkovDeFinettiHardEulerTrailFiber
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHardExcursionBridge
open Mettapedia.Logic.MarkovDeFinettiHardBESTCore
open Mettapedia.Logic.EvidenceDirichlet

variable {k : ℕ}

/-- `W(N, s, θ) = |fiber(N, s)| × wordProb(θ, xs₀)` for any `xs₀ ∈ fiber(N, s)`,
since `wordProb` is constant on the fiber. -/
lemma W_eq_card_mul_wordProb_of_mem_fiber
    {N : ℕ} (θ : MarkovParam k) (s : MarkovState k)
    (xs₀ : Traj k N) (hxs₀ : xs₀ ∈ fiber k N s) :
    W (k := k) N s θ =
      (fiber k N s).card *
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
  classical
  simp only [W]
  have hfib : (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s) = fiber k N s := rfl
  rw [hfib]
  have hconst : ∀ xs ∈ fiber k N s,
      wordProb (k := k) θ (trajToList (k := k) xs) =
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
    intro xs hxs
    exact wordProb_const_on_state_fiber (k := k) θ
      (by rw [(Finset.mem_filter.1 hxs).2, (Finset.mem_filter.1 hxs₀).2])
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  simp [nsmul_eq_mul]

/-! ## Pattern index set `P(n,e,s)` and decomposition identities -/

/-- Finite excursion-prefix pattern set `P(n,e,s)`.

It includes:
1. patterns coming from long-horizon prefix fibers (`prefixFiber(hN,e,s)`), and
2. all short-horizon WR patterns in `fiber(n+1,e)`.

This shared index set lets the WOR and WR decompositions range over one finite
carrier; WR then has no residual term outside `P`. -/
def excursionPatternSet
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) : Finset (ExcursionList k) :=
  ((prefixFiber (k := k) (h := hN) e s).image
    (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))) ∪
  ((fiber k (Nat.succ n) e).image
    (fun ys => excursionListOfTraj (k := k) ys))

lemma mem_excursionPatternSet_of_prefixFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    {xs : Traj k N} (hxs : xs ∈ prefixFiber (k := k) (h := hN) e s) :
    excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) ∈
      ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)) := by
  refine Finset.mem_image.2 ?_
  refine ⟨trajPrefix (k := k) hN xs, ?_, rfl⟩
  have hstate : prefixState (k := k) hN xs = e := (Finset.mem_filter.1 hxs).2
  have htraj : trajPrefix (k := k) hN xs ∈ trajFinset k (Nat.succ n) := by
    simp [trajFinset]
  exact Finset.mem_filter.2 ⟨htraj, by simpa [prefixState] using hstate⟩

lemma excursionPatternSet_eq_shortImage
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    excursionPatternSet (k := k) (hN := hN) e s =
      ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)) := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    rcases Finset.mem_union.1 hp with hpL | hpR
    · rcases Finset.mem_image.1 hpL with ⟨xs, hxs, rfl⟩
      exact mem_excursionPatternSet_of_prefixFiber (k := k) (hN := hN) (e := e) (s := s) hxs
    · exact hpR
  · intro hp
    exact Finset.mem_union.2 (Or.inr hp)

/-- The `p`-fiber inside `prefixFiber(hN,e,s)`. -/
def prefixPatternFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    Finset (Traj k N) :=
  (prefixFiber (k := k) (h := hN) e s).filter
    (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p)

lemma segmentSwap_mem_prefixPatternFiber_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (xs : Traj k N) (hxs : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
      prefixPatternFiber (k := k) (hN := hN) e s p := by
  have hxs_pf : xs ∈ prefixFiber (k := k) (h := hN) e s := (Finset.mem_filter.1 hxs).1
  have hmem_pf :
      segmentSwap xs a L1 L2 hL1 hL2 hcN ∈ prefixFiber (k := k) (h := hN) e s :=
    segmentSwap_mem_prefixFiber_of_prefix_before_swap
      (k := k) (h := hN) (e := e) (eN := s) (xs := xs)
      (a := a) (L1 := L1) (L2 := L2) (hna := hna)
      (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
      (ha_ret := ha_ret) (hb_ret := hb_ret) (hc_ret := hc_ret) hxs_pf
  have hpat : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
    (Finset.mem_filter.1 hxs).2
  have hprefix_eq :
      trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        trajPrefix (k := k) hN xs :=
    trajPrefix_segmentSwap_eq_of_prefix_before_swap
      (k := k) (h := hN) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      (hna := hna) (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
  refine Finset.mem_filter.2 ?_
  refine ⟨hmem_pf, ?_⟩
  simpa [hprefix_eq] using hpat

lemma card_image_segmentSwap_prefixPatternFiber_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (_hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    ((prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card =
      (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
  classical
  refine Finset.card_image_iff.mpr ?_
  intro x hx y hy hxy
  exact segmentSwap_injective (k := k) (a := a) (L1 := L1) (L2 := L2)
    (hL1 := hL1) (hL2 := hL2) (hcN := hcN) hxy

/-- Build an image-equality witness for prefix-pattern fibers from
forward/backward segment-swap membership maps. -/
lemma image_eq_segmentSwap_prefixPatternFiber_of_maps
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (p q : ExcursionList k)
    (a L1 L2 : ℕ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (hmap :
      ∀ xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p,
        segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
          prefixPatternFiber (k := k) (hN := hN) e s q)
    (hmapInv :
      ∀ ys ∈ prefixPatternFiber (k := k) (hN := hN) e s q,
        segmentSwap ys a L2 L1 hL2 hL1 (by omega) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p) :
    (prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN) =
      prefixPatternFiber (k := k) (hN := hN) e s q := by
  classical
  apply Finset.Subset.antisymm
  · intro ys hys
    rcases Finset.mem_image.1 hys with ⟨xs, hxs, rfl⟩
    exact hmap xs hxs
  · intro ys hys
    refine Finset.mem_image.2 ?_
    refine ⟨segmentSwap ys a L2 L1 hL2 hL1 (by omega), hmapInv ys hys, ?_⟩
    simpa using
      (segmentSwap_involutive (k := k) ys a L2 L1 hL2 hL1 (by omega))

/-- WOR-side mass for pattern `p`: cardinality ratio in the long-horizon fiber. -/
def worPatternMass
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
    ((fiber k N s).card : ENNReal)

/-- Pattern ratio inside the long-prefix fiber:
`|prefixPatternFiber(hN,e,s,p)| / |prefixFiber(hN,e,s)|`. -/
def prefixPatternRatio
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
    ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)

/-- WR-side mass for pattern `p`: indicator-sum over short trajectories in `fiber(n+1,e)`. -/
def wrPatternMass
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ∑ ys ∈ fiber k (Nat.succ n) e,
    if excursionListOfTraj (k := k) ys = p then
      wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys)
    else 0

/-- The short-horizon trajectories in state `e` with excursion list exactly `p`. -/
def shortPatternFiber
    (n : ℕ) (e : MarkovState k) (p : ExcursionList k) : Finset (Traj k (Nat.succ n)) :=
  (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p)

end MarkovDeFinettiHardBEST
end Mettapedia.Logic
