import Mettapedia.Languages.GF.Core
import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.Typing
import Mettapedia.Languages.GF.LinguisticInvariance
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Logic.OSLFEvidenceSemantics

/-!
# Evidence-Grounded Semantics for GF via World Models

This module bridges GF abstract syntax trees to evidence-valued denotations
via the PLN world-model interface.  The key construction:

  ⟦t⟧_W := WorldModel.evidence W (queryOfAtom a (gfAbstractToPattern t))

World-model states W replace possible worlds; Evidence values (n⁺, n⁻)
replace truth values.  OSLF modalities (◇, □) still run over the rewrite
graph, but atom meaning comes from evidence extraction.

## Design choices

- **Query type**: `Query = Pattern` (patterns are the queries)
- **Atom encoding**: `queryOfAtom : String → Pattern → Pattern` tags patterns
  with atom names, so different atoms at the same pattern get distinct queries
- **Atom interpretation**: Prop-threshold on `Evidence.toStrength`

## Assumptions

1. Query extraction totality: `queryOfAtom` is total on all atom-pattern pairs
2. Threshold monotonicity: lower threshold → more atoms satisfied (proved)
3. Query encoding: atom names are incorporated into the query pattern
-/

namespace Mettapedia.Languages.GF.WorldModelSemantics

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.LinguisticInvariance
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Logic.OSLFEvidenceSemantics

open scoped ENNReal

/-! ## 1. Atom-Query Encoder

The encoder maps (atom name, pattern) pairs to Pattern queries.
Different atoms at the same pattern produce different queries,
so the world model can assign different evidence to each. -/

/-- Encode an atom name and a pattern into a query pattern.
The atom name is incorporated as a tag so that different atoms
at the same pattern produce different queries. -/
def queryOfAtom (atomName : String) (p : Pattern) : Pattern :=
  .apply ("atom:" ++ atomName) [p]

/-- Different atom names produce different queries at the same pattern. -/
theorem queryOfAtom_injective_name (a₁ a₂ : String) (p : Pattern)
    (h : a₁ ≠ a₂) : queryOfAtom a₁ p ≠ queryOfAtom a₂ p := by
  unfold queryOfAtom
  intro heq
  injection heq with h1 _
  simp [String.ext_iff] at h1
  exact h (String.ext h1)

/-! ## 7. Garden-Path Query Distinction

Two structurally different parses produce different query patterns.
(Placed before the section so these concrete defs don't inherit section variables.) -/

/-- Garden-path parse 1: "The old man walks" (adjective reading). -/
private def gpParse1 : AbstractNode := mkApp2 "PredVP" "NP" "VP" "Cl"
  (mkApp2 "DetCN" "Det" "CN" "NP"
    (mkLeaf "the_Det" "Det")
    (mkApp2 "AdjCN" "AP" "CN" "CN"
      (mkApp1 "PositA" "A" "AP" (mkLeaf "old" "A"))
      (mkApp1 "UseN" "N" "CN" (mkLeaf "man" "N"))))
  (mkApp1 "UseV" "V" "VP" (mkLeaf "walk" "V"))

/-- Garden-path parse 2: "The old mans the boat" (verb reading). -/
private def gpParse2 : AbstractNode := mkApp2 "PredVP" "NP" "VP" "Cl"
  (mkApp2 "DetCN" "Det" "CN" "NP"
    (mkLeaf "the_Det" "Det")
    (mkApp1 "UseN" "N" "CN" (mkLeaf "old" "N")))
  (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
    (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "man" "V2"))
    (mkApp2 "DetCN" "Det" "CN" "NP"
      (mkLeaf "the_Det" "Det")
      (mkApp1 "UseN" "N" "CN" (mkLeaf "boat" "N"))))

/-- The two garden-path parses produce different OSLF patterns. -/
theorem garden_path_queries_differ :
    gfAbstractToPattern gpParse1 ≠ gfAbstractToPattern gpParse2 := by
  simp [gpParse1, gpParse2, mkApp2, mkApp1, mkLeaf, List.map]

section GFSemantics

variable {State : Type*} [EvidenceType State] [WorldModel State Pattern]

/-! ## 2. Core Definitions -/

/-- Evidence-valued denotation of a GF abstract tree in world-model state W.

`⟦t⟧_W = evidence(W, gfAbstractToPattern(t))`. -/
noncomputable def gfEvidenceDenote (W : State) (t : AbstractNode) : Evidence :=
  WorldModel.evidence W (gfAbstractToPattern t)

/-- Threshold-based atom semantics grounded in a world-model state.

An atom `a` holds at pattern `p` iff
`toStrength(evidence W (queryOfAtom a p)) ≥ threshold`.
The atom name is part of the query, so different atoms can have
different evidence. -/
noncomputable def gfAtomSemFromWM (W : State) (threshold : ℝ≥0∞) : AtomSem :=
  fun atomName p =>
    threshold ≤ Evidence.toStrength (WorldModel.evidence W (queryOfAtom atomName p))

/-- Full OSLF formula semantics grounded in a world-model state.

Uses `langReduces gfRGLLanguageDef` (= `langReducesUsing .empty gfRGLLanguageDef`)
as the reduction relation, matching `checkLangUsing_sat_sound`. -/
noncomputable def gfWMFormulaSem
    (W : State) (threshold : ℝ≥0∞)
    (φ : OSLFFormula) (p : Pattern) : Prop :=
  sem (langReduces gfRGLLanguageDef) (gfAtomSemFromWM W threshold) φ p

/-! ## 3. Checker Soundness → WM Semantics

The existing `checkLangUsing_sat_sound` bridges the bounded model checker
to denotational semantics.  We instantiate it with WM-grounded atoms. -/

/-- If the OSLF checker returns `.sat` with an atom checker sound w.r.t.
the WM-grounded atom semantics, then the formula holds in the WM-grounded
denotational semantics.

This is the central soundness bridge: it connects the executable checker
to the evidence-valued semantic layer. -/
theorem oslf_sat_implies_wm_semantics
    (W : State) (threshold : ℝ≥0∞)
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true →
      (gfAtomSemFromWM W threshold) a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkLangUsing .empty gfRGLLanguageDef I_check fuel p φ = .sat) :
    gfWMFormulaSem W threshold φ p :=
  checkLangUsing_sat_sound h_atoms h

/-! ## 4. Evidence Revision Preserves Denotation

Evidence extraction commutes with revision (`+`) in the world-model state.
This is the key structural property: combining evidence sources is coherent
with denotation. -/

/-- Revising two world-model states and then extracting evidence for a GF tree
equals extracting evidence from each and combining via hplus. -/
theorem evidence_denote_revision (W₁ W₂ : State) (t : AbstractNode) :
    gfEvidenceDenote (W₁ + W₂) t =
      gfEvidenceDenote W₁ t + gfEvidenceDenote W₂ t := by
  simp only [gfEvidenceDenote]
  exact WorldModel.evidence_add W₁ W₂ (gfAbstractToPattern t)

/-! ## 5. Threshold Antitonicity

Lowering the threshold makes more atoms satisfied.  This is a genuine
structural theorem about the atom interpretation layer. -/

/-- If the WM atom semantics holds at threshold τ₂, it also holds at
any lower threshold τ₁ ≤ τ₂. -/
theorem atom_threshold_antitone
    (W : State) (τ₁ τ₂ : ℝ≥0∞) (h_le : τ₁ ≤ τ₂)
    (a : String) (p : Pattern)
    (h_sat : (gfAtomSemFromWM W τ₂) a p) :
    (gfAtomSemFromWM W τ₁) a p :=
  le_trans h_le h_sat

/-- Threshold antitonicity lifts to atom checker soundness:
if all checked atoms hold at τ₂, they hold at τ₁ ≤ τ₂. -/
theorem atom_check_threshold_antitone
    (W : State) (τ₁ τ₂ : ℝ≥0∞) (h_le : τ₁ ≤ τ₂)
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true →
      (gfAtomSemFromWM W τ₂) a p) :
    ∀ a p, I_check a p = true →
      (gfAtomSemFromWM W τ₁) a p :=
  fun a p hc => atom_threshold_antitone W τ₁ τ₂ h_le a p (h_atoms a p hc)

/-! ## 6. WM Query Judgment Bridge

From a WM judgment (derivable posterior state) to evidence extraction on
GF abstract trees.  This connects the PLN inference calculus to GF semantics. -/

/-- A derivable world-model state yields a well-formed query judgment
for any GF abstract tree. -/
theorem gf_wm_query_judgment
    (W : State) (t : AbstractNode) (hW : WMJudgment W) :
    WMQueryJudgment W (gfAbstractToPattern t) (gfEvidenceDenote W t) :=
  ⟨hW, rfl⟩

/-- Combining two derivable states yields a derivable query judgment
with combined evidence (via `evidence_add`). -/
theorem gf_wm_query_revise
    {W₁ W₂ : State} (t : AbstractNode)
    (h₁ : WMQueryJudgment W₁
      (gfAbstractToPattern t) (gfEvidenceDenote W₁ t))
    (h₂ : WMQueryJudgment W₂
      (gfAbstractToPattern t) (gfEvidenceDenote W₂ t)) :
    WMQueryJudgment (W₁ + W₂)
      (gfAbstractToPattern t)
      (gfEvidenceDenote W₁ t + gfEvidenceDenote W₂ t) :=
  WMJudgment.query_revise h₁ h₂

/-- Different patterns → different evidence in any discriminating world model.
Combined with `garden_path_queries_differ`, this shows the two parses
can be semantically distinguished by evidence. -/
theorem garden_path_evidence_separable
    (W : State)
    (h_disc : WorldModel.evidence W (gfAbstractToPattern gpParse1) ≠
              WorldModel.evidence W (gfAbstractToPattern gpParse2)) :
    gfEvidenceDenote W gpParse1 ≠ gfEvidenceDenote W gpParse2 :=
  h_disc

/-! ## 8. Lexical Containment Monotonicity

Delegates to proved lexical monotonicity theorems.  In the evidence domain:
if a lexical item is query-accessible in a pattern, it remains accessible
after modification. -/

/-- Adjective modification preserves lexical containment. -/
theorem wm_lexical_containment_monotone
    (adjName : String) (cn : AbstractNode) (name : String)
    (h : containsLexical name (gfAbstractToPattern cn) = true) :
    containsLexical name (gfAbstractToPattern (addAdjModifier adjName cn)) = true :=
  adjModification_preserves_lexical adjName cn name h

/-- Modification adds the adjective as new lexical content. -/
theorem wm_adjective_adds_lexical (adjName : String) (cn : AbstractNode) :
    containsLexical adjName (gfAbstractToPattern (addAdjModifier adjName cn)) = true :=
  adjModification_adds_adjective adjName cn

/-! ## 9. Evidence-Valued GF Semantics (Primary Layer)

The threshold-Prop semantics above (`gfWMFormulaSem`) is a derived view.
The PRIMARY semantics maps formulas to Evidence values via `semE` from
`OSLFEvidenceSemantics.lean`, using the Frame structure of Evidence
(⊓ for ∧, ⊔ for ∨, ⇨ for →, ⨆ for ◇, ⨅ for □). -/

/-- Evidence-valued atom semantics from a world-model state.
Each atom name and pattern produces an Evidence value via WM query. -/
noncomputable def gfEvidenceAtomSemFromWM (W : State) : EvidenceAtomSem :=
  wmEvidenceAtomSem W queryOfAtom

/-- Full evidence-valued OSLF formula semantics for GF.

This is the PRIMARY semantic layer: formulas map to Evidence, not Prop.
The threshold-Prop semantics `gfWMFormulaSem` is a corollary obtained by
thresholding this. -/
noncomputable def gfWMFormulaSemE
    (W : State) (φ : OSLFFormula) (p : Pattern) : Evidence :=
  semE (langReduces gfRGLLanguageDef) (gfEvidenceAtomSemFromWM W) φ p

/-- The threshold-Prop atom semantics is recovered by thresholding the
evidence-valued atom semantics on `Evidence.toStrength`. -/
theorem gfAtomSemFromWM_eq_threshold (W : State) (threshold : ℝ≥0∞)
    (a : String) (p : Pattern) :
    gfAtomSemFromWM W threshold a p ↔
      threshold ≤ Evidence.toStrength (gfEvidenceAtomSemFromWM W a p) := by
  rfl

/-- Evidence revision lifts to GF evidence atoms:
combining world-model states then extracting = extracting then combining. -/
theorem gfWMFormulaSemE_atom_revision (W₁ W₂ : State) (a : String) (p : Pattern) :
    gfWMFormulaSemE (W₁ + W₂) (.atom a) p =
      gfWMFormulaSemE W₁ (.atom a) p + gfWMFormulaSemE W₂ (.atom a) p := by
  simp only [gfWMFormulaSemE, semE_atom, gfEvidenceAtomSemFromWM, wmEvidenceAtomSem]
  exact WorldModel.evidence_add W₁ W₂ (queryOfAtom a p)

/-- Conjunction in evidence semantics projects to components. -/
theorem gfWMFormulaSemE_and_le_left (W : State) (φ ψ : OSLFFormula) (p : Pattern) :
    gfWMFormulaSemE W (.and φ ψ) p ≤ gfWMFormulaSemE W φ p := by
  exact semE_and_le_left _ _ _ _ _

/-- Diamond witnesses inject into evidence diamond. -/
theorem gfWMFormulaSemE_dia_le (W : State) (φ : OSLFFormula) (p q : Pattern)
    (h : langReduces gfRGLLanguageDef p q) :
    gfWMFormulaSemE W φ q ≤ gfWMFormulaSemE W (.dia φ) p := by
  exact semE_dia_le _ _ _ _ _ h

/-- GF evidence denote is a direct WM query, while gfEvidenceAtomSemFromWM goes
through the atom-tagged query encoding. They share the same WM extraction
mechanism but on different query patterns. -/
theorem gfEvidenceDenote_as_evidence (W : State) (t : AbstractNode) :
    gfEvidenceDenote W t =
      WorldModel.evidence W (gfAbstractToPattern t) := by
  rfl

end GFSemantics

end Mettapedia.Languages.GF.WorldModelSemantics
