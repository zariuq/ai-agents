import Mettapedia.Languages.MeTTa.RuntimeSpec
import Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary
import Mettapedia.Languages.ProcessCalculi.MORK.Conformance

/-!
# MeTTa Runtime Execution Surface

Packages the first concrete runtime-execution backend surface, `R_exec₀`, around
the existing theoremic MORK/MM2 execution boundary.

`RuntimeSpec.lean` remains audit-facing and dialect-facing.  This file sits one
layer lower: it records the backend-facing fragment predicate, translations, and
the first source-rule execution bridge we already know how to prove.

Positive example:
- MORK can execute source-rule firings for the proven `morkTranslatable`
  fragment, and that fact is packaged here as `morkRuntimeExec0`.

Negative example:
- this file does not redefine `A`, does not claim runtime completeness, and does
  not smuggle scheduler/priority metadata into `RuntimeSpec`.
-/

namespace Mettapedia.Languages.MeTTa.RuntimeExec

open Mettapedia.Languages.MeTTa.Core (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary

private abbrev ILP :=
  Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILRRule :=
  Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILDL :=
  Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
private abbrev ILPremise :=
  Mettapedia.OSLF.MeTTaIL.Syntax.Premise
private abbrev ILBind :=
  Mettapedia.OSLF.MeTTaIL.Match.Bindings
private abbrev ILRelEnv :=
  Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv
private abbrev CSpace :=
  Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.CSpace

/-- First source-rule firing contract used by the current `R_exec₀` surface.

This packages exactly the theorem already proved for the no-premise, `fvar`-LHS
fragment of `DeclReducesWithPremises`.
-/
abbrev RuntimeExecNoPremiseSourceBridge : Prop :=
  ∀ (p q : ILP) (x : String)
      (r : ILRRule) (_relEnv : ILRelEnv) (_lang : ILDL)
      (_hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
      (_htrans_rhs : fragmentPredicate r.right = true)
      (_hnoprem : r.premises = [])
      (bs : ILBind) (_hbs : bs ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
      (_hrhs : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
      (_hground : isGroundAtom (patternTranslation q) = true)
      (s : Space) (_hp_in : patternTranslation p ∈ s),
      applySinks s (bindingsTranslation bs) (sourceRuleTranslation r).tmpl ∈
        fireSourceRule s (sourceRuleTranslation r)

/-- Premise-aware source-rule firing contract already available at the current
`R_exec₀` level for relation-query-only premise chains. -/
abbrev RuntimeExecMultiPremiseSourceBridge : Prop :=
  ∀ (p q : ILP) (x : String)
      (r : ILRRule) (relEnv : ILRelEnv) (lang : ILDL)
      (_hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
      (_htrans_rhs : fragmentPredicate r.right = true)
      (_htrans_prem : premiseTranslatability r.premises = true)
      (bs0 : ILBind) (_hbs0 : bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
      (bs : ILBind)
      (_hrhs : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
      (_hground : isGroundAtom (patternTranslation q) = true)
      (s : Space) (_hp_in : patternTranslation p ∈ s)
      (witnesses : List Atom)
      (_hchain : premiseChainType relEnv lang s bs0 r.premises witnesses bs)
      (_hnodup : witnesses.Nodup)
      (_hwit_ne_p : ∀ a ∈ witnesses, a ≠ patternTranslation p),
      applySinks s (bindingsTranslation bs) (sourceRuleTranslation r).tmpl ∈
        fireSourceRule s (sourceRuleTranslation r)

/-- Guard-aware source-rule firing contract already available at the current
execution boundary for mixed relationQuery/freshness premise chains. This is
the future-facing theorem seam above raw MM2 execution and below any richer
runtime fragment packaging. -/
abbrev RuntimeExecGuardedSourceBridge : Prop :=
  ∀ (p q : ILP) (x : String)
      (r : ILRRule) (relEnv : ILRelEnv) (lang : ILDL)
      (_hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
      (_htrans_rhs : fragmentPredicate r.right = true)
      (_htrans_prem : extendedTranslatability r.premises = true)
      (bs0 : ILBind) (_hbs0 : bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p)
      (bs : ILBind)
      (_hrhs : Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs r.right = q)
      (_hground : isGroundAtom (patternTranslation q) = true)
      (s : Space) (_hp_in : patternTranslation p ∈ s)
      (witnesses : List Atom)
      (_hchain : premiseChainType relEnv lang s bs0 r.premises witnesses bs)
      (_hnodup : witnesses.Nodup)
      (_hwit_ne_p : ∀ a ∈ witnesses, a ≠ patternTranslation p)
      (_hguards : matchSourceGuardsDef (bindingsTranslation bs)
          (sourceGuardExtraction r.premises) = true),
      applySinks s (bindingsTranslation bs) (extendedRuleTranslation r).tmpl ∈
        fireSourceRule s (extendedRuleTranslation r)

/-- First theoremic backend surface for MeTTa-family runtime execution. -/
structure MeTTaRuntimeExecSurface where
  backendName : String
  objectLanguage : String
  fragmentPredicate : ILP → Bool
  patternTranslation : ILP → Atom
  spaceInjection : ILP → Space
  bindingsTranslation : ILBind → Subst
  sourceRuleTranslation : ILRRule → SourceExecRule
  sourceRuleSetTranslation : ILDL → List SourceExecRule
  noPremiseBridge : RuntimeExecNoPremiseSourceBridge

/-- Extended theoremic execution surface over the same backend. This packages
the already-proved premise-aware and guard-aware source-rule bridges without
changing the live runtime semantics. -/
structure MeTTaRuntimeExecExtendedSurface extends MeTTaRuntimeExecSurface where
  premiseTranslatability : List ILPremise → Bool
  extendedPremiseTranslatability : List ILPremise → Bool
  sourceGuardExtraction : List ILPremise → List SourceGuard
  extendedSourceRuleTranslation : ILRRule → SourceExecRule
  extendedSourceRuleSetTranslation : ILDL → List SourceExecRule
  multiPremiseBridge : RuntimeExecMultiPremiseSourceBridge
  guardedBridge : RuntimeExecGuardedSourceBridge

/-- Query-side sibling of the current theoremic runtime execution surface.

`R_exec₀` packages source-rule firing. This packages the lower-level source-query
machinery that the same MORK/MM2 backend already provides. It is the honest seam
for runtime features such as `match &self`, which are source queries rather than
rewrite firings.

Positive example:
- `matchSourceFactor` and `cmatchSourceFactor` already agree on the same backend.

Negative example:
- this does not claim that source queries are themselves rewrite steps.
-/
structure MeTTaRuntimeQuerySurface where
  backendName : String
  objectLanguage : String
  patternTranslation : ILP → Atom
  bindingsTranslation : ILBind → Subst
  workspaceTranslation : CSpace → Space
  baseSourceFactor : ILP → SourceFactor
  sourceFactorMatch : Subst → Space → SourceFactor → List (Subst × Atom)
  computableSourceFactorMatch : Subst → CSpace → SourceFactor → List (Subst × Atom)
  sourceFactorSound :
    ∀ (σ : Subst) (s : CSpace) (src : SourceFactor) (σ' : Subst) (a : Atom),
      (σ', a) ∈ computableSourceFactorMatch σ s src →
      (σ', a) ∈ sourceFactorMatch σ (workspaceTranslation s) src
  sourceFactorComplete :
    ∀ (σ : Subst) (s : CSpace) (src : SourceFactor) (σ' : Subst) (a : Atom),
      (σ', a) ∈ sourceFactorMatch σ (workspaceTranslation s) src →
      (σ', a) ∈ computableSourceFactorMatch σ s src

/-- Canonical `R_exec₀`: the current theoremic MORK/MM2 execution boundary for
MeTTaIL source rules. -/
def morkRuntimeExec0 : MeTTaRuntimeExecSurface where
  backendName := "MORK/MM2"
  objectLanguage := "MeTTaIL"
  fragmentPredicate := fragmentPredicate
  patternTranslation := patternTranslation
  spaceInjection := spaceInjection
  bindingsTranslation := bindingsTranslation
  sourceRuleTranslation := sourceRuleTranslation
  sourceRuleSetTranslation := sourceRuleSetTranslation
  noPremiseBridge := noPremiseBridge

/-- Canonical extended `R_exec₀`: the same MORK/MM2 backend, now packaged with
its already-proved premise-aware and guard-aware theoremic bridges. -/
def morkRuntimeExec0Ext : MeTTaRuntimeExecExtendedSurface where
  toMeTTaRuntimeExecSurface := morkRuntimeExec0
  premiseTranslatability := Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.premiseTranslatability
  extendedPremiseTranslatability := Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.extendedTranslatability
  sourceGuardExtraction := Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.sourceGuardExtraction
  extendedSourceRuleTranslation := Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.extendedRuleTranslation
  extendedSourceRuleSetTranslation := Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.languageDefSourceRulesExt
  multiPremiseBridge := Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.multiPremiseBridge
  guardedBridge := Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.multiPremiseExtBridge

/-- Canonical query-side sibling of `R_exec₀`: the MORK/MM2 source-query seam.

This is the right backend target for PeTTa `spaceQuery` fragments and any later
runtime feature that fundamentally asks for source matching rather than source
rule firing.
-/
noncomputable def morkRuntimeQueryExec0 : MeTTaRuntimeQuerySurface where
  backendName := "MORK/MM2"
  objectLanguage := "MeTTaIL"
  patternTranslation := patternTranslation
  bindingsTranslation := bindingsTranslation
  workspaceTranslation := List.toFinset
  baseSourceFactor := fun p => .btm (patternTranslation p)
  sourceFactorMatch := matchSourceFactor
  computableSourceFactorMatch :=
    fun σ s src =>
      Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable.cmatchSourceFactor
        σ s.dedup src
  sourceFactorSound := by
    intro σ s src σ' a h
    have hsnd :=
      Mettapedia.Languages.ProcessCalculi.MORK.Conformance.cmatchSourceFactor_sound
        σ s.dedup src (List.nodup_dedup s) σ' a h
    have hs_toFinset : s.dedup.toFinset = s.toFinset := by
      ext a
      simp [List.mem_dedup]
    simpa [hs_toFinset] using hsnd
  sourceFactorComplete := by
    intro σ s src σ' a h
    have hs_toFinset : s.dedup.toFinset = s.toFinset := by
      ext a
      simp [List.mem_dedup]
    have h' : (σ', a) ∈ matchSourceFactor σ s.dedup.toFinset src := by
      simpa [hs_toFinset] using h
    exact
      Mettapedia.Languages.ProcessCalculi.MORK.Conformance.cmatchSourceFactor_complete
        σ s.dedup src σ' a h'

theorem morkRuntimeExec0_backendName :
    morkRuntimeExec0.backendName = "MORK/MM2" := rfl

theorem morkRuntimeExec0_objectLanguage :
    morkRuntimeExec0.objectLanguage = "MeTTaIL" := rfl

theorem morkRuntimeExec0_fragmentPredicate :
    morkRuntimeExec0.fragmentPredicate = fragmentPredicate := rfl

theorem morkRuntimeExec0_sourceRuleTranslation :
    morkRuntimeExec0.sourceRuleTranslation = sourceRuleTranslation := rfl

theorem morkRuntimeExec0_sourceRuleSetTranslation :
    morkRuntimeExec0.sourceRuleSetTranslation = sourceRuleSetTranslation := rfl

theorem morkRuntimeExec0_noPremiseBridge :
    morkRuntimeExec0.noPremiseBridge = noPremiseBridge := rfl

theorem morkRuntimeExec0Ext_extendedPremiseTranslatability :
    morkRuntimeExec0Ext.extendedPremiseTranslatability =
      Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.extendedTranslatability := rfl

theorem morkRuntimeExec0Ext_sourceGuardExtraction :
    morkRuntimeExec0Ext.sourceGuardExtraction =
      Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.sourceGuardExtraction := rfl

theorem morkRuntimeExec0Ext_extendedSourceRuleTranslation :
    morkRuntimeExec0Ext.extendedSourceRuleTranslation =
      Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.extendedRuleTranslation := rfl

theorem morkRuntimeExec0Ext_multiPremiseBridge :
    morkRuntimeExec0Ext.multiPremiseBridge =
      Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.multiPremiseBridge := rfl

theorem morkRuntimeExec0Ext_guardedBridge :
    morkRuntimeExec0Ext.guardedBridge =
      Mettapedia.Languages.ProcessCalculi.MORK.ExecutionBoundary.multiPremiseExtBridge := rfl

theorem morkRuntimeQueryExec0_backendName :
    morkRuntimeQueryExec0.backendName = "MORK/MM2" := rfl

theorem morkRuntimeQueryExec0_baseSourceFactor :
    morkRuntimeQueryExec0.baseSourceFactor = fun p => SourceFactor.btm (patternTranslation p) := rfl

end Mettapedia.Languages.MeTTa.RuntimeExec
