import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNBayesNetFastRules
import Mettapedia.Logic.EvidenceBeta

/-!
# PLN Xi Derived BN Rules (No-Sly Admissibility)

Concrete, fully derived PLN inference rules for the chain Bayesian network model.
Every rule's side condition is derived from **model semantics** (local Markov property
+ d-separation), not taken as a free hypothesis.

## Architecture: 5-Shape Derived Rule Block

Each rule family provides all 5 shapes:

1. **Side condition derivation** — derive Σ from BN model semantics
2. **WMRewriteRule** — the concrete rule (NO free `hSO` argument)
3. **Admissibility** — query judgment from derivable WM state
4. **OSLF evidence bridge** — `semE` equals derived evidence
5. **Threshold bridge** — strength-threshold Prop holds

## Scope

Currently covers **deduction** (chain A→B→C) only. Source (fork) and sink
(collider) rules require new BN graph structure proofs not yet in the codebase.

## Concrete Proofs Used

All building blocks are fully proved (0 sorry):
- `chain_screeningOff_wmqueryeq_of_dsep` (PLNBNCompilation)
- `chain_screeningOff_strength_eq_of_dsep` (PLNBNCompilation)
- `queryStrength_singleton_eq_queryProb` (PLNBNCompilation)
- `linkProbVE_eq_jointMeasure_eventEq` / `propProbVE_eq_jointMeasure_eventEq` (VEBridge)
- `chainBN_plnDeductionStrength_exact` (PLNBayesNetFastRules)
- `evidence_aggregation_is_conjugate_update` (EvidenceBeta)

0 sorry. All theorems fully proved.
-/

namespace Mettapedia.Logic.PLNXiDerivedBNRules

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.PLNBNCompilation
open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.Logic.PLNBNCompilation.ChainExample
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax

open scoped Classical ENNReal

/-! ## §0 Type Aliases -/

/-- All CPTs in the chain BN satisfy the local Markov property. -/
abbrev ChainBNLocalMarkovAll
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace] :=
  ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure

/-! ## §1 Deduction: Chain BN (A→B→C)

All arguments are model-semantic:
- `hLMarkov` : every CPT satisfies the local Markov property (a BN model axiom)
- `hDSep` : A and C are d-separated given B (a graph-theoretic property)

Neither is "assume the conclusion." The screening-off equality is a
**consequence** of these, proved in PLNBNCompilation. -/

section ChainBNDeduction

variable
  [∀ v : Three, Fintype (chainBN.stateSpace v)]
  [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
  [∀ v : Three, Inhabited (chainBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
  [StandardBorelSpace chainBN.JointSpace]

/-! ### Shape 1: Side condition derivation -/

/-- The screening-off query equivalence for the chain BN deduction case,
derived from local Markov + d-separation. -/
theorem deduction_wmqueryeq_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN)) :
    WMQueryEq (State := BNWorldModel.State (bn := chainBN))
      (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
      (PLNQuery.linkCond
        [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
        ⟨Three.C, valC⟩)
      (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
  chain_screeningOff_wmqueryeq_of_dsep
    (valA := valA) (valB := valB) (valC := valC) hLMarkov hDSep

/-! ### Shape 2: Derived WMRewriteRule (NO free hSO argument) -/

/-- Deduction rewrite rule for the chain BN, derived from local Markov +
d-separation. The rule rewrites `linkCond [A,B] C` to `link B C`.

Arguments are model-semantic:
- `hLMarkov` : local Markov property (BN model axiom)
- `hDSep` : d-separation A ⊥ C | B (graph property)

There is NO abstract screening-off hypothesis. -/
noncomputable def xi_deduction_rewrite_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (PLNQuery (BNQuery.Atom (bn := chainBN))) :=
  dsep_rewrite
    (State := BNWorldModel.State (bn := chainBN))
    (Atom := BNQuery.Atom (bn := chainBN))
    (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩)
    (PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    ((CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN))
    (fun h => (deduction_wmqueryeq_of_chainBN valA valB valC hLMarkov h).symm)

/-- The derived rule's side condition is exactly d-separation. -/
theorem xi_deduction_rewrite_of_chainBN_side
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN)) :
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).side :=
  hDSep

/-! ### Shape 3: Admissibility (actual inference theorem) -/

/-- Admissibility: for any derivable WM state, the deduction rule produces
a valid query judgment. This is the "PLN deduction is sound in chain BNs"
theorem. -/
theorem xi_deduction_admissible_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (W : BNWorldModel.State (bn := chainBN))
    (hW : ⊢wm W) :
    ⊢q W ⇓
      (PLNQuery.linkCond
        ([ (⟨Three.A, valA⟩ : BNQuery.Atom (bn := chainBN))
         , (⟨Three.B, valB⟩ : BNQuery.Atom (bn := chainBN)) ])
        (⟨Three.C, valC⟩ : BNQuery.Atom (bn := chainBN))) ↦
      (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).derive W :=
  WMRewriteRule.apply
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep) hW

/-! ### Shape 4: OSLF evidence bridge -/

/-- OSLF evidence bridge: if the OSLF atom encodes the deduction conclusion,
its evidence equals the derived rule's output. -/
theorem xi_deduction_semE_atom_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := chainBN))
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := chainBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩) :
    semE R
      (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov)
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep)
    W enc a p hEnc

/-! ### Shape 5: Threshold bridge -/

/-- Threshold bridge: if the derived strength exceeds `tau`, the atom
holds under strength-threshold semantics. -/
theorem xi_deduction_threshold_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := chainBN))
    (tau : ℝ≥0∞)
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := chainBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    (hTau : tau ≤ Evidence.toStrength
      ((xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).derive W)) :
    sem R
      (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov)
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep)
    W tau enc a p hEnc hTau

/-! ### Bonus: Strength equality (re-export from PLNBNCompilation) -/

/-- Strength equality: under d-separation, the linkCond and link queries
have identical strength in every WM state. -/
theorem xi_deduction_strength_eq_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (W : BNWorldModel.State (bn := chainBN)) :
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := chainBN))
      (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
      W (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
      =
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := chainBN))
      (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
      W (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
  chain_screeningOff_strength_eq_of_dsep
    (valA := valA) (valB := valB) (valC := valC) hLMarkov hDSep W

end ChainBNDeduction

/-! ## §2 Tier B: Bernoulli-PLN Bridge (Measure → Formula)

Connects the measure-level conditional probability `P(C|A)` to the
`plnDeductionStrength` formula. This is a re-export of
`chainBN_plnDeductionStrength_exact` (PLNBayesNetFastRules) with Xi naming,
plus the foundational lemma `toStrength_evidenceOfProb` that links the
WM evidence layer to probability values.

### Evidence ↔ Probability Bridge

`BNWorldModel` stores evidence as `evidenceOfProb(p) = ⟨p, 1-p⟩` where
`p` is the conditional probability (ENNReal). `Evidence.toStrength` recovers
`p` when `p ≤ 1` (proved: `toStrength_evidenceOfProb`).

**Note**: The full singleton-CPT bridge (`queryStrength {cpt} q = queryProb cpt q`)
requires composing multiset singleton lemmas with `toStrength_evidenceOfProb`.
This is proved in PLNBNCompilation as `queryStrength_singleton_eq_queryProb`.

### PLN Deduction Strength Exactness

Under the chain BN screening-off conditions (derived from d-sep + local Markov):

```
P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))
```

This is `chainBN_plnDeductionStrength_exact` (PLNBayesNetFastRules.lean). -/

section TierB

open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNBayesNetFastRules
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN.Deduction
open MeasureTheory

/-- Evidence ↔ Probability bridge: `toStrength` of `evidenceOfProb p` recovers `p`
when `p ≤ 1`. This is the foundational lemma connecting WM evidence to probability. -/
theorem toStrength_evidenceOfProb (p : ℝ≥0∞) (hp : p ≤ 1) :
    Evidence.toStrength (evidenceOfProb p) = p := by
  unfold Evidence.toStrength evidenceOfProb Evidence.total
  simp only
  split
  · rename_i h
    have : p + (1 - p) = 1 := by rw [add_comm]; exact tsub_add_cancel_of_le hp
    rw [this] at h; exact absurd h one_ne_zero
  · have : p + (1 - p) = 1 := by rw [add_comm]; exact tsub_add_cancel_of_le hp
    rw [this]; exact div_one p

/-- Tier B: In the chain BN, the conditional probability `P(C|A)` equals the PLN
deduction formula applied to the component conditional probabilities.

This is the measure-level bridge connecting BN semantics to the algebraic
`plnDeductionStrength` formula. Re-exported from `chainBN_plnDeductionStrength_exact`
with Xi naming for the 3-tier theorem spine.

Arguments:
- `cpt` : a discrete CPT for the chain BN
- Positivity conditions on events A, B, A∩B, A∩Bᶜ (non-degeneracy)
- `hB_lt1` : P(B) < 1 (ensures P(Bᶜ) > 0) -/
theorem xi_deduction_plnStrength_exact_of_chainBN
    (cpt : PLNBayesNetFastRules.ChainBN.DiscreteCPT)
    (hA_pos : (μ (cpt := cpt)) (A : Set ChainBN.JointSpace) ≠ 0)
    (hB_pos : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) ≠ 0)
    (hB_lt1 : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) < 1)
    (hAB_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) ≠ 0)
    (hABc_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) ≠ 0) :
    (μ (cpt := cpt)).real (C ∩ (A : Set ChainBN.JointSpace)) /
        (μ (cpt := cpt)).real (A : Set ChainBN.JointSpace) =
      plnDeductionStrength
        ((μ (cpt := cpt)).real ((B : Set ChainBN.JointSpace) ∩ A) /
            (μ (cpt := cpt)).real (A : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)) /
            (μ (cpt := cpt)).real (B : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (B : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (C : Set ChainBN.JointSpace)) :=
  chainBN_plnDeductionStrength_exact (cpt := cpt) hA_pos hB_pos hB_lt1 hAB_pos hABc_pos

end TierB

/-! ## §2b Tier A→B Composition: queryStrength → plnDeductionStrength

End-to-end composition connecting the WM queryStrength layer (ENNReal) to the
algebraic plnDeductionStrength formula (ℝ) for the chain BN.

### Bridge Chain

```
queryStrength {cpt} q  (ENNReal)
  ↓ singleton bridge (queryStrength_singleton_eq_queryProb)
queryProb cpt q  (ENNReal)
  ↓ VEBridge (linkProbVE/propProbVE_eq_jointMeasure_eventEq)
μ(event₁ ∩ event₂) / μ(event₁)  (ENNReal)
  ↓ ENNReal.toReal_div + Measure.real
μ.real ratios  (ℝ)
  ↓ chainBN_plnDeductionStrength_exact
plnDeductionStrength(s_AB, s_BC, s_B, s_C)  (ℝ)
```

**Consumes**: singleton bridge, VEBridge, Tier B. -/

section TierAB

open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNBayesNetFastRules
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN.Deduction
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open MeasureTheory

variable
  [∀ v : Three, Fintype (chainBN.stateSpace v)]
  [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
  [∀ v : Three, Inhabited (chainBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
  [StandardBorelSpace chainBN.JointSpace]

/-! ### Bridge lemmas: VEBridge types ↔ FastRules types -/

set_option linter.unusedSectionVars false in
/-- `eventEq v true` (VEBridge) equals `eventTrue v` (FastRules). -/
private lemma eventEq_true_eq_eventTrue (v : Three) :
    eventEq (bn := chainBN) v true = eventTrue v := by
  ext ω; simp [eventEq, eventTrue, Set.mem_preimage]

/-! ### Bridge lemmas: queryProb → jointMeasure -/

/-- queryProb for prop at `true` = marginal measure μ(event). -/
private lemma queryProb_prop_true_eq
    (cpt : ChainBN.DiscreteCPT) (v : Three) :
    queryProb (bn := chainBN) cpt (PLNQuery.prop ⟨v, true⟩) =
      (μ (cpt := cpt)) (eventTrue v) := by
  simp only [queryProb]
  rw [propProbVE_eq_jointMeasure_eventEq, eventEq_true_eq_eventTrue]
  rfl

/-- queryProb for link at `true` = conditional probability ratio μ(a∩b)/μ(a). -/
private lemma queryProb_link_true_eq
    (cpt : ChainBN.DiscreteCPT) (a b : Three)
    (ha : (μ (cpt := cpt)) (eventTrue a) ≠ 0) :
    queryProb (bn := chainBN) cpt (PLNQuery.link ⟨a, true⟩ ⟨b, true⟩) =
      (μ (cpt := cpt)) (eventTrue a ∩ eventTrue b) /
        (μ (cpt := cpt)) (eventTrue a) := by
  simp only [queryProb]
  rw [linkProbVE_eq_jointMeasure_eventEq]
  simp only [eventEq_true_eq_eventTrue]
  split_ifs with h
  · exact absurd h ha
  · rfl

/-! ### Probability bounds (needed by singleton bridge) -/

private lemma queryProb_prop_true_le_one
    (cpt : ChainBN.DiscreteCPT) (v : Three) :
    queryProb (bn := chainBN) cpt (PLNQuery.prop ⟨v, true⟩) ≤ 1 := by
  rw [queryProb_prop_true_eq]; exact prob_le_one

private lemma queryProb_link_true_le_one
    (cpt : ChainBN.DiscreteCPT) (a b : Three) :
    queryProb (bn := chainBN) cpt (PLNQuery.link ⟨a, true⟩ ⟨b, true⟩) ≤ 1 := by
  simp only [queryProb]
  rw [linkProbVE_eq_jointMeasure_eventEq]
  simp only [eventEq_true_eq_eventTrue]
  split
  · exact zero_le_one
  · exact le_trans (ENNReal.div_le_div_right (measure_mono Set.inter_subset_left) _)
      ENNReal.div_self_le_one

/-! ### ENNReal → ℝ bridge: queryStrength.toReal = μ.real -/

/-- Singleton prop queryStrength.toReal = μ.real(event). -/
private lemma queryStrength_singleton_prop_toReal
    (cpt : ChainBN.DiscreteCPT) (v : Three) :
    (WorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := chainBN))
      (PLNQuery.prop (⟨v, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    (μ (cpt := cpt)).real (eventTrue v) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (queryProb_prop_true_le_one cpt v)]
  rw [queryProb_prop_true_eq]
  simp [Measure.real]

/-- Singleton link queryStrength.toReal = μ.real(b∩a)/μ.real(a).
Note: intersection order is b∩a (not a∩b) to match Tier B convention. -/
private lemma queryStrength_singleton_link_toReal
    (cpt : ChainBN.DiscreteCPT) (a b : Three)
    (ha : (μ (cpt := cpt)) (eventTrue a) ≠ 0) :
    (WorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := chainBN))
      (PLNQuery.link (⟨a, true⟩ : BNQuery.Atom (bn := chainBN))
                     (⟨b, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    (μ (cpt := cpt)).real (eventTrue b ∩ eventTrue a) /
      (μ (cpt := cpt)).real (eventTrue a) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (queryProb_link_true_le_one cpt a b)]
  rw [queryProb_link_true_eq cpt a b ha]
  rw [Set.inter_comm (eventTrue a) (eventTrue b)]
  rw [ENNReal.toReal_div]
  simp [Measure.real]

/-! ### Composition theorem -/

/-- **Tier A→B Composition**: For the chain BN with singleton CPT state,
the PLN deduction probability identity holds at the queryStrength level:

```
P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))
```

where each probability is `(queryStrength {cpt} q).toReal`.

**Consumes**:
- `queryStrength_singleton_eq_queryProb` (singleton bridge)
- `linkProbVE_eq_jointMeasure_eventEq` / `propProbVE_eq_jointMeasure_eventEq` (VEBridge)
- `chainBN_plnDeductionStrength_exact` (Tier B) -/
theorem xi_deduction_queryStrength_eq_plnDeduction_of_chainBN
    (cpt : ChainBN.DiscreteCPT)
    (hA_pos : (μ (cpt := cpt)) (A : Set ChainBN.JointSpace) ≠ 0)
    (hB_pos : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) ≠ 0)
    (hB_lt1 : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) < 1)
    (hAB_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) ≠ 0)
    (hABc_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) ≠ 0) :
    let W : BNWorldModel.State (bn := chainBN) := {cpt}
    (WorldModel.queryStrength W
      (PLNQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
                     (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    plnDeductionStrength
      (WorldModel.queryStrength W
        (PLNQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
                       (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.link (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN))
                       (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.prop (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.prop (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal := by
  intro W
  -- Bridge: convert each queryStrength to μ.real
  rw [queryStrength_singleton_link_toReal cpt Three.A Three.C hA_pos]
  rw [queryStrength_singleton_link_toReal cpt Three.A Three.B hA_pos]
  rw [queryStrength_singleton_link_toReal cpt Three.B Three.C hB_pos]
  rw [queryStrength_singleton_prop_toReal cpt Three.B]
  rw [queryStrength_singleton_prop_toReal cpt Three.C]
  -- Now goal is in μ.real terms, matching Tier B exactly
  exact chainBN_plnDeductionStrength_exact (cpt := cpt) hA_pos hB_pos hB_lt1 hAB_pos hABc_pos

end TierAB

/-! ## §3 Tier C: Beta-Bernoulli Computational Layer

When evidence is represented as discrete counts `(n⁺, n⁻)`, the PLN strength
function `plnStrength` computes `n⁺/(n⁺+n⁻)`. Substituting these into
`plnDeductionStrength` gives a fully computable expression.

**Guardrail**: The Beta distribution is a *modeling choice*, not forced by
exchangeability. See `EvidenceBeta.not_beta_from_exchangeability_example`
for an explicit counterexample: an exchangeable sequence whose de Finetti
mixing measure is NOT Beta. -/

section TierC

open Mettapedia.Logic.PLN
open Mettapedia.Logic.EvidenceBeta

/-! ### Denominator safety -/

/-- `plnStrength n⁺ n⁻ < 1` when `n⁻ ≠ 0`. This ensures the denominator
`(1 - s_B)` in `plnDeductionStrength` is positive. -/
theorem plnStrength_lt_one (n_pos n_neg : ℕ) (hNeg : n_neg ≠ 0) :
    plnStrength n_pos n_neg < 1 := by
  unfold plnStrength
  split
  · exact zero_lt_one
  · rename_i hTotal
    rw [div_lt_one (by positivity : (0 : ℝ) < ↑n_pos + ↑n_neg)]
    have : (0 : ℝ) < ↑n_neg := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hNeg)
    linarith

/-- The denominator `(1 - s_B)` in `plnDeductionStrength` is positive
when `nB_neg ≠ 0`. -/
theorem plnDeductionStrength_denom_pos (n_pos n_neg : ℕ) (hNeg : n_neg ≠ 0) :
    0 < 1 - plnStrength n_pos n_neg :=
  sub_pos.mpr (plnStrength_lt_one n_pos n_neg hNeg)

/-! ### Count-based unfolding -/

/-- Tier C: `plnDeductionStrength` applied to `plnStrength` count values
unfolds to the same formula with rational arguments `n⁺/(n⁺+n⁻)`.

This makes PLN deduction fully computable from evidence counts alone.
The proof is definitional unfolding of `plnStrength`. -/
theorem plnDeductionStrength_of_plnStrength
    (nAB_pos nAB_neg nBC_pos nBC_neg nB_pos nB_neg nC_pos nC_neg : ℕ)
    (hAB : nAB_pos + nAB_neg ≠ 0) (hBC : nBC_pos + nBC_neg ≠ 0)
    (hB : nB_pos + nB_neg ≠ 0) :
    plnDeductionStrength
      (plnStrength nAB_pos nAB_neg)
      (plnStrength nBC_pos nBC_neg)
      (plnStrength nB_pos nB_neg)
      (plnStrength nC_pos nC_neg) =
    plnDeductionStrength
      ((nAB_pos : ℝ) / (↑nAB_pos + ↑nAB_neg))
      ((nBC_pos : ℝ) / (↑nBC_pos + ↑nBC_neg))
      ((nB_pos : ℝ) / (↑nB_pos + ↑nB_neg))
      (plnStrength nC_pos nC_neg) := by
  simp only [plnStrength, hAB, hBC, hB, ↓reduceIte]

/-- Tier C (full unfold): All four `plnStrength` values unfolded. -/
theorem plnDeductionStrength_of_plnStrength_full
    (nAB_pos nAB_neg nBC_pos nBC_neg nB_pos nB_neg nC_pos nC_neg : ℕ)
    (hAB : nAB_pos + nAB_neg ≠ 0) (hBC : nBC_pos + nBC_neg ≠ 0)
    (hB : nB_pos + nB_neg ≠ 0) (hC : nC_pos + nC_neg ≠ 0) :
    plnDeductionStrength
      (plnStrength nAB_pos nAB_neg)
      (plnStrength nBC_pos nBC_neg)
      (plnStrength nB_pos nB_neg)
      (plnStrength nC_pos nC_neg) =
    plnDeductionStrength
      ((nAB_pos : ℝ) / (↑nAB_pos + ↑nAB_neg))
      ((nBC_pos : ℝ) / (↑nBC_pos + ↑nBC_neg))
      ((nB_pos : ℝ) / (↑nB_pos + ↑nB_neg))
      ((nC_pos : ℝ) / (↑nC_pos + ↑nC_neg)) := by
  simp only [plnStrength, hAB, hBC, hB, hC, ↓reduceIte]

/-- Tier C connection to conjugate update: evidence aggregation (hplus) is
Beta conjugate update. See `EvidenceBeta.evidence_aggregation_is_conjugate_update`.

**Guardrail**: Beta is a modeling choice. See
`EvidenceBeta.not_beta_from_exchangeability_example` for a counterexample
showing exchangeability does NOT force the Beta distribution. -/
theorem evidence_hplus_is_conjugate :
    ∀ (prior_param : ℝ) (hprior : 0 < prior_param)
      (n₁_pos n₁_neg n₂_pos n₂_neg : ℕ),
    let params₁ := { prior_param := prior_param, prior_pos := hprior,
                     evidence_pos := n₁_pos, evidence_neg := n₁_neg :
                     EvidenceBetaParams }
    let params_combined := { prior_param := prior_param, prior_pos := hprior,
                             evidence_pos := n₁_pos + n₂_pos,
                             evidence_neg := n₁_neg + n₂_neg :
                             EvidenceBetaParams }
    params_combined.alpha = params₁.alpha + ↑n₂_pos ∧
    params_combined.beta = params₁.beta + ↑n₂_neg :=
  evidence_aggregation_is_conjugate_update

end TierC

/-! ## §4 Source / Sink Rules: Honest Status

Source rule (induction) requires fork BN (B→A, B→C) screening-off proof.
Sink rule (abduction) requires collider BN (A→B←C) screening-off proof.

Neither exists in the codebase. The formula decompositions
(`plnInduction_eq_bayes_deduction`, `plnAbduction_eq_bayes_deduction`)
and structural decompositions (`SourceRuleBayesDed`, `SinkRuleBayesDed`)
exist in PLNDerivation.lean and PLNXiRuleRegistry.lean, but the concrete
BN measure-level proofs for fork/collider graphs are missing.

To derive source/sink rules, we would need:
1. Define fork/collider BN graph structures (like `chainBN` for chains)
2. Prove measure-level screening-off for those structures
3. Bridge to WMQueryEq via conditional independence
4. Then wrap in the 5-shape block

This is tracked but not disguised as done. -/

end Mettapedia.Logic.PLNXiDerivedBNRules
