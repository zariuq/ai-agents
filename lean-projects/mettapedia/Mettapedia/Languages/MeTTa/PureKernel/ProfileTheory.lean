import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# PureKernel Profile-Theory Layer (C1)

This file defines the profile-side theory closure for MeTTa-Pure:

- a sealed base step relation with the current Pure kernel β rules
- pure `Pattern` contexts (`PurePatCtx`)
- contextual closure (`PureProfileTheoryStep`)
- reflexive-transitive closure (`PureProfileTheoryStepStar`)

This is the C1 layer in the A/B/C architecture.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core

/-- Reflexive-transitive closure of profile-level one-step reduction for `mettaPure`. -/
abbrev PureProfileStepStar (p q : Pattern) : Prop :=
  Relation.ReflTransGen (langReduces mettaPure) p q

/-- Sealed base one-step relation for the pure profile:
the current Pure kernel β rules at the `Pattern` level. -/
inductive PureProfileBaseStep : Pattern → Pattern → Prop where
  | betaPi (body a : Pattern) :
      PureProfileBaseStep (mkApp (mkLam body) a) (openBVar 0 a body)
  | betaSigmaFst (a b : Pattern) :
      PureProfileBaseStep (mkFst (mkPair a b)) a
  | betaSigmaSnd (a b : Pattern) :
      PureProfileBaseStep (mkSnd (mkPair a b)) b
  | betaUnitRec (motive unitCase : Pattern) :
      PureProfileBaseStep (mkUnitRec motive unitCase mkUnitMk) unitCase
  | betaBoolRecFalse (motive falseCase trueCase : Pattern) :
      PureProfileBaseStep (mkBoolRec motive falseCase trueCase mkBoolFalse) falseCase
  | betaBoolRecTrue (motive falseCase trueCase : Pattern) :
      PureProfileBaseStep (mkBoolRec motive falseCase trueCase mkBoolTrue) trueCase
  | betaNatRecZero (motive zeroCase succCase : Pattern) :
      PureProfileBaseStep (mkNatRec motive zeroCase succCase mkNatZero) zeroCase
  | betaNatRecSucc (motive zeroCase succCase k : Pattern) :
      PureProfileBaseStep (mkNatRec motive zeroCase succCase (mkNatSucc k))
        (mkApp (mkApp succCase k) (mkNatRec motive zeroCase succCase k))

private def betaPiRule : RewriteRule :=
  { name := "BetaPi",
    typeContext := [("body", .base "Tm"), ("a", .base "Tm")],
    premises := [],
    left := .apply "App" [.apply "Lam" [.lambda (.fvar "body")], .fvar "a"],
    right := .subst (.fvar "body") (.fvar "a") }

private def betaSigmaFstRule : RewriteRule :=
  { name := "BetaSigmaFst",
    typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
    premises := [],
    left := .apply "Fst" [.apply "Pair" [.fvar "a", .fvar "b"]],
    right := .fvar "a" }

private def betaSigmaSndRule : RewriteRule :=
  { name := "BetaSigmaSnd",
    typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
    premises := [],
    left := .apply "Snd" [.apply "Pair" [.fvar "a", .fvar "b"]],
    right := .fvar "b" }

private def betaUnitRecRule : RewriteRule :=
  { name := "BetaUnitRec",
    typeContext := [("motive", .base "Tm"), ("unitCase", .base "Tm")],
    premises := [],
    left := .apply "UnitRec" [.fvar "motive", .fvar "unitCase", .apply "UnitMk" []],
    right := .fvar "unitCase" }

private def betaBoolRecFalseRule : RewriteRule :=
  { name := "BetaBoolRecFalse",
    typeContext := [("motive", .base "Tm"), ("falseCase", .base "Tm"), ("trueCase", .base "Tm")],
    premises := [],
    left := .apply "BoolRec"
      [.fvar "motive", .fvar "falseCase", .fvar "trueCase", .apply "BoolFalse" []],
    right := .fvar "falseCase" }

private def betaBoolRecTrueRule : RewriteRule :=
  { name := "BetaBoolRecTrue",
    typeContext := [("motive", .base "Tm"), ("falseCase", .base "Tm"), ("trueCase", .base "Tm")],
    premises := [],
    left := .apply "BoolRec"
      [.fvar "motive", .fvar "falseCase", .fvar "trueCase", .apply "BoolTrue" []],
    right := .fvar "trueCase" }

private def betaNatRecZeroRule : RewriteRule :=
  { name := "BetaNatRecZero",
    typeContext := [("motive", .base "Tm"), ("zeroCase", .base "Tm"), ("succCase", .base "Tm")],
    premises := [],
    left := .apply "NatRec"
      [.fvar "motive", .fvar "zeroCase", .fvar "succCase", .apply "NatZero" []],
    right := .fvar "zeroCase" }

private def betaNatRecSuccRule : RewriteRule :=
  { name := "BetaNatRecSucc",
    typeContext := [("motive", .base "Tm"), ("zeroCase", .base "Tm"), ("succCase", .base "Tm"), ("k", .base "Tm")],
    premises := [],
    left := .apply "NatRec"
      [.fvar "motive", .fvar "zeroCase", .fvar "succCase", .apply "NatSucc" [.fvar "k"]],
    right := .apply "App"
      [.apply "App" [.fvar "succCase", .fvar "k"],
       .apply "NatRec" [.fvar "motive", .fvar "zeroCase", .fvar "succCase", .fvar "k"]] }

/-- Sealed base steps are sound for profile one-step reduction. -/
theorem pureProfileBaseStep_sound_langReduces {s t : Pattern}
    (h : PureProfileBaseStep s t) :
    langReduces mettaPure s t := by
  cases h with
  | betaPi body a =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaPiRule, ?_, ?_⟩
      · simp [betaPiRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("a", a), ("body", body)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaPiRule, mkApp, mkLam, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaPiRule]
          · simp [bs, betaPiRule, applyBindings]
  | @betaSigmaFst aa bb =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaSigmaFstRule, ?_, ?_⟩
      · simp [betaSigmaFstRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("b", bb), ("a", t)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaSigmaFstRule, mkFst, mkPair, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaSigmaFstRule]
          · simp [bs, betaSigmaFstRule, applyBindings]
  | @betaSigmaSnd aa bb =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaSigmaSndRule, ?_, ?_⟩
      · simp [betaSigmaSndRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("b", t), ("a", aa)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaSigmaSndRule, mkSnd, mkPair, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaSigmaSndRule]
          · simp [bs, betaSigmaSndRule, applyBindings]
  | betaUnitRec motive _ =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaUnitRecRule, ?_, ?_⟩
      · simp [betaUnitRecRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("unitCase", t), ("motive", motive)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaUnitRecRule, mkUnitRec, mkUnitMk, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaUnitRecRule]
          · simp [bs, betaUnitRecRule, applyBindings]
  | betaBoolRecFalse motive _ trueCase =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaBoolRecFalseRule, ?_, ?_⟩
      · simp [betaBoolRecFalseRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("falseCase", t), ("trueCase", trueCase), ("motive", motive)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaBoolRecFalseRule, mkBoolRec, mkBoolFalse, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaBoolRecFalseRule]
          · simp [bs, betaBoolRecFalseRule, applyBindings]
  | betaBoolRecTrue motive falseCase _ =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaBoolRecTrueRule, ?_, ?_⟩
      · simp [betaBoolRecTrueRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("falseCase", falseCase), ("trueCase", t), ("motive", motive)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaBoolRecTrueRule, mkBoolRec, mkBoolTrue, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaBoolRecTrueRule]
          · simp [bs, betaBoolRecTrueRule, applyBindings]
  | betaNatRecZero motive _ succCase =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaNatRecZeroRule, ?_, ?_⟩
      · simp [betaNatRecZeroRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("zeroCase", t), ("succCase", succCase), ("motive", motive)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaNatRecZeroRule, mkNatRec, mkNatZero, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaNatRecZeroRule]
          · simp [bs, betaNatRecZeroRule, applyBindings]
  | @betaNatRecSucc motive zeroCase succCase k =>
      apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := mettaPure)
      unfold langReducesExecUsing rewriteWithContextWithPremisesUsing rewriteStepWithPremisesUsing
      apply List.mem_append.mpr
      left
      rw [List.mem_flatMap]
      refine ⟨betaNatRecSuccRule, ?_, ?_⟩
      · simp [betaNatRecSuccRule, mettaPure]
      · unfold applyRuleWithPremisesUsing
        rw [List.mem_flatMap]
        let bs : Bindings := [("zeroCase", zeroCase), ("k", k), ("succCase", succCase), ("motive", motive)]
        refine ⟨bs, ?_, ?_⟩
        · simp [bs, betaNatRecSuccRule, mkNatRec, mkNatSucc, matchPattern, matchArgs, mergeBindings]
        · rw [List.mem_map]
          refine ⟨bs, ?_, ?_⟩
          · simp [applyPremisesWithEnv, bs, betaNatRecSuccRule]
          · simp [bs, betaNatRecSuccRule, applyBindings, mkApp, mkNatRec]

/-- Pure term-contexts on the `Pattern` side (C1): exactly the constructor positions
corresponding to kernel congruence (`Red`). -/
inductive PurePatCtx : Type where
  | hole : PurePatCtx
  | piDom (K : PurePatCtx) (B : Pattern) : PurePatCtx
  | piCod (A : Pattern) (K : PurePatCtx) : PurePatCtx
  | sigmaDom (K : PurePatCtx) (B : Pattern) : PurePatCtx
  | sigmaCod (A : Pattern) (K : PurePatCtx) : PurePatCtx
  | idTy (K : PurePatCtx) (a b : Pattern) : PurePatCtx
  | idLeft (A : Pattern) (K : PurePatCtx) (b : Pattern) : PurePatCtx
  | idRight (A a : Pattern) (K : PurePatCtx) : PurePatCtx
  | lam (K : PurePatCtx) : PurePatCtx
  | appFun (K : PurePatCtx) (a : Pattern) : PurePatCtx
  | appArg (f : Pattern) (K : PurePatCtx) : PurePatCtx
  | pairFst (K : PurePatCtx) (b : Pattern) : PurePatCtx
  | pairSnd (a : Pattern) (K : PurePatCtx) : PurePatCtx
  | fst (K : PurePatCtx) : PurePatCtx
  | snd (K : PurePatCtx) : PurePatCtx
  | refl (K : PurePatCtx) : PurePatCtx
  | natSucc (K : PurePatCtx) : PurePatCtx
  | unitRecMotive (K : PurePatCtx) (unitCase scrutinee : Pattern) : PurePatCtx
  | unitRecCase (motive : Pattern) (K : PurePatCtx) (scrutinee : Pattern) : PurePatCtx
  | unitRecScrutinee (motive unitCase : Pattern) (K : PurePatCtx) : PurePatCtx
  | boolRecMotive (K : PurePatCtx) (falseCase trueCase scrutinee : Pattern) : PurePatCtx
  | boolRecFalseCase (motive : Pattern) (K : PurePatCtx) (trueCase scrutinee : Pattern) : PurePatCtx
  | boolRecTrueCase (motive falseCase : Pattern) (K : PurePatCtx) (scrutinee : Pattern) : PurePatCtx
  | boolRecScrutinee (motive falseCase trueCase : Pattern) (K : PurePatCtx) : PurePatCtx
  | natRecMotive (K : PurePatCtx) (zeroCase succCase scrutinee : Pattern) : PurePatCtx
  | natRecZeroCase (motive : Pattern) (K : PurePatCtx) (succCase scrutinee : Pattern) : PurePatCtx
  | natRecSuccCase (motive zeroCase : Pattern) (K : PurePatCtx) (scrutinee : Pattern) : PurePatCtx
  | natRecScrutinee (motive zeroCase succCase : Pattern) (K : PurePatCtx) : PurePatCtx
  | close (x : String) (K : PurePatCtx) : PurePatCtx

/-- Plug a `Pattern` into a pure term-context. -/
def plugPurePatCtx : PurePatCtx → Pattern → Pattern
  | .hole, p => p
  | .piDom K B, p => mkPi (plugPurePatCtx K p) B
  | .piCod A K, p => mkPi A (plugPurePatCtx K p)
  | .sigmaDom K B, p => mkSigma (plugPurePatCtx K p) B
  | .sigmaCod A K, p => mkSigma A (plugPurePatCtx K p)
  | .idTy K a b, p => mkId (plugPurePatCtx K p) a b
  | .idLeft A K b, p => mkId A (plugPurePatCtx K p) b
  | .idRight A a K, p => mkId A a (plugPurePatCtx K p)
  | .lam K, p => mkLam (plugPurePatCtx K p)
  | .appFun K a, p => mkApp (plugPurePatCtx K p) a
  | .appArg f K, p => mkApp f (plugPurePatCtx K p)
  | .pairFst K b, p => mkPair (plugPurePatCtx K p) b
  | .pairSnd a K, p => mkPair a (plugPurePatCtx K p)
  | .fst K, p => mkFst (plugPurePatCtx K p)
  | .snd K, p => mkSnd (plugPurePatCtx K p)
  | .refl K, p => mkRefl (plugPurePatCtx K p)
  | .natSucc K, p => mkNatSucc (plugPurePatCtx K p)
  | .unitRecMotive K unitCase scrutinee, p => mkUnitRec (plugPurePatCtx K p) unitCase scrutinee
  | .unitRecCase motive K scrutinee, p => mkUnitRec motive (plugPurePatCtx K p) scrutinee
  | .unitRecScrutinee motive unitCase K, p => mkUnitRec motive unitCase (plugPurePatCtx K p)
  | .boolRecMotive K falseCase trueCase scrutinee, p =>
      mkBoolRec (plugPurePatCtx K p) falseCase trueCase scrutinee
  | .boolRecFalseCase motive K trueCase scrutinee, p =>
      mkBoolRec motive (plugPurePatCtx K p) trueCase scrutinee
  | .boolRecTrueCase motive falseCase K scrutinee, p =>
      mkBoolRec motive falseCase (plugPurePatCtx K p) scrutinee
  | .boolRecScrutinee motive falseCase trueCase K, p =>
      mkBoolRec motive falseCase trueCase (plugPurePatCtx K p)
  | .natRecMotive K zeroCase succCase scrutinee, p =>
      mkNatRec (plugPurePatCtx K p) zeroCase succCase scrutinee
  | .natRecZeroCase motive K succCase scrutinee, p =>
      mkNatRec motive (plugPurePatCtx K p) succCase scrutinee
  | .natRecSuccCase motive zeroCase K scrutinee, p =>
      mkNatRec motive zeroCase (plugPurePatCtx K p) scrutinee
  | .natRecScrutinee motive zeroCase succCase K, p =>
      mkNatRec motive zeroCase succCase (plugPurePatCtx K p)
  | .close x K, p => closeFVar 0 x (plugPurePatCtx K p)

/-- C1 one-step profile-theory relation:
least contextual closure (under pure contexts) of the sealed base β rules. -/
inductive PureProfileTheoryStep : Pattern → Pattern → Prop where
  | base {s t : Pattern} :
      PureProfileBaseStep s t →
      PureProfileTheoryStep s t
  | ctx {K : PurePatCtx} {s t : Pattern} :
      PureProfileTheoryStep s t →
      PureProfileTheoryStep (plugPurePatCtx K s) (plugPurePatCtx K t)

/-- C1 star closure. -/
abbrev PureProfileTheoryStepStar (p q : Pattern) : Prop :=
  Relation.ReflTransGen PureProfileTheoryStep p q

/-- Any sealed base step is a C1 step. -/
theorem pureProfileBaseStep_to_pureProfileTheoryStep {s t : Pattern}
    (h : PureProfileBaseStep s t) :
    PureProfileTheoryStep s t :=
  .base h

/-- Any sealed base step is a C1-star step. -/
theorem pureProfileBaseStep_to_pureProfileTheoryStepStar {s t : Pattern}
    (h : PureProfileBaseStep s t) :
    PureProfileTheoryStepStar s t :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl (.base h)

end Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory
