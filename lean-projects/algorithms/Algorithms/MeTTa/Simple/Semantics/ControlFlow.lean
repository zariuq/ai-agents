import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.ControlFlow

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  eval : σ → Pattern → σ × List Pattern
  evalKeyValues : σ → Pattern → σ × List Pattern
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  evalCallableApply : σ → Pattern → List Pattern → σ × List Pattern
  evalGeneratorValues : σ → Pattern → σ × List Pattern
  isTruthy : Pattern → Bool
  patternOfBool : Bool → Pattern

structure Preservation (I : Interface σ) (P : σ → Prop) where
  eval_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.eval s term = (s', out) →
      P s → P s'
  evalKeyValues_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.evalKeyValues s term = (s', out) →
      P s → P s'
  evalCallableApply_preserves :
    ∀ {s : σ} {fn : Pattern} {args : List Pattern} {s' : σ} {out : List Pattern},
      I.evalCallableApply s fn args = (s', out) →
      P s → P s'
  evalGeneratorValues_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.evalGeneratorValues s term = (s', out) →
      P s → P s'

private theorem foldlState_preserves
    (P : σ → Prop)
    (step : (σ × α) → β → (σ × α))
    (hStep : ∀ (st : σ × α) (x : β), P st.1 → P (step st x).1)
    (xs : List β) (st : σ × α) :
    P st.1 → P ((xs.foldl step st).1) := by
  intro hP
  induction xs generalizing st with
  | nil =>
      simpa
  | cons x xs ih =>
      have hStep' : P (step st x).1 := hStep st x hP
      simpa [List.foldl] using ih (step st x) hStep'

private def decodeCasePair? : Pattern → Option (Pattern × Pattern)
  | .apply "Expr" [pat, value] => some (pat, value)
  | .apply ctor [value] =>
      let pat :=
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then .apply ctor [] else .fvar name
        else
          .apply ctor []
      some (pat, value)
  | _ => none

private def decodeCasePairs? : Pattern → Option (List (Pattern × Pattern))
  | .apply "Expr" elems => elems.mapM decodeCasePair?
  | .collection _ elems _ => elems.mapM decodeCasePair?
  | one =>
      match decodeCasePair? one with
      | some p => some [p]
      | none => none

private def isCaseDefaultPattern : Pattern → Bool
  | .apply "Empty" [] => true
  | .apply "empty" [] => true
  | _ => false

private def evalCaseValueBindingStep (I : Interface σ) (value : Pattern)
    (acc : σ × List Pattern) (bs : Bindings) : σ × List Pattern :=
  let sess := acc.1
  let outAcc := acc.2
  let valueSub := I.applyBindings bs value
  let (sess', out) := I.eval sess valueSub
  let out' := if out.isEmpty then [valueSub] else out
  (sess', outAcc ++ out')

private theorem evalCaseValueBindingStep_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (value : Pattern) (acc : σ × List Pattern) (bs : Bindings) :
    P acc.1 → P (evalCaseValueBindingStep I value acc bs).1 := by
  intro hP
  unfold evalCaseValueBindingStep
  exact H.eval_preserves rfl hP

private def evalCaseValueForBindings (I : Interface σ) (s : σ)
    (value : Pattern) (subs : List Bindings) : σ × List Pattern :=
  subs.foldl (evalCaseValueBindingStep I value) (s, [])

private theorem evalCaseValueForBindings_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (value : Pattern) (subs : List Bindings) :
    P s → P (evalCaseValueForBindings I s value subs).1 := by
  intro hP
  unfold evalCaseValueForBindings
  exact foldlState_preserves P (evalCaseValueBindingStep I value)
    (evalCaseValueBindingStep_preserves I P H value) subs (s, []) hP

private def evalCaseTryBranches (I : Interface σ)
    (defaultPair? : Option (Pattern × Pattern))
    (key : Pattern) (sess : σ) : List (Pattern × Pattern) → σ × List Pattern × Bool
  | [] =>
      match defaultPair? with
      | some (_, defaultVal) =>
          let (sess', outDef) := I.eval sess defaultVal
          let out' := if outDef.isEmpty then [defaultVal] else outDef
          (sess', out', true)
      | none =>
          (sess, [], false)
  | (pat, value) :: rest =>
      let subs := I.matchPattern pat key
      if subs.isEmpty then
        evalCaseTryBranches I defaultPair? key sess rest
      else
        let (sess', outCase) := evalCaseValueForBindings I sess value subs
        (sess', outCase, true)

private theorem evalCaseTryBranches_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (defaultPair? : Option (Pattern × Pattern))
    (key : Pattern) (sess : σ) (pairs : List (Pattern × Pattern)) :
    P sess → P (evalCaseTryBranches I defaultPair? key sess pairs).1 := by
  intro hP
  induction pairs generalizing sess with
  | nil =>
      unfold evalCaseTryBranches
      cases defaultPair? with
      | none =>
          simpa
      | some kv =>
          exact H.eval_preserves rfl hP
  | cons pair rest ih =>
      rcases pair with ⟨pat, value⟩
      unfold evalCaseTryBranches
      by_cases hSubs : (I.matchPattern pat key).isEmpty
      · simp [hSubs]
        exact ih sess hP
      · simp [hSubs]
        exact evalCaseValueForBindings_preserves I P H sess value (I.matchPattern pat key) hP

private def evalCaseKeyStep (I : Interface σ)
    (defaultPair? : Option (Pattern × Pattern))
    (normalPairs : List (Pattern × Pattern))
    (acc : σ × List Pattern) (key : Pattern) : σ × List Pattern :=
  let sess := acc.1
  let outAcc := acc.2
  let (sess', outCase, _) := evalCaseTryBranches I defaultPair? key sess normalPairs
  (sess', outAcc ++ outCase)

private theorem evalCaseKeyStep_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (defaultPair? : Option (Pattern × Pattern))
    (normalPairs : List (Pattern × Pattern))
    (acc : σ × List Pattern) (key : Pattern) :
    P acc.1 → P (evalCaseKeyStep I defaultPair? normalPairs acc key).1 := by
  intro hP
  unfold evalCaseKeyStep
  exact evalCaseTryBranches_preserves I P H defaultPair? key acc.1 normalPairs hP

def evalCaseIntrinsic (I : Interface σ) (s : σ)
    (keyExpr branchesExpr : Pattern) : σ × List Pattern :=
  let (sK, keyOut) := I.evalKeyValues s keyExpr
  let keys := if keyOut.isEmpty then [keyExpr] else keyOut
  let pairs := decodeCasePairs? branchesExpr
  match pairs with
  | none =>
      (sK, [.apply "case" [keyExpr, branchesExpr]])
  | some rawPairs =>
      let normalPairs := rawPairs.filter (fun kv => !isCaseDefaultPattern kv.1)
      let defaultPair? := rawPairs.find? (fun kv => isCaseDefaultPattern kv.1)
      keys.foldl (evalCaseKeyStep I defaultPair? normalPairs) (sK, [])

theorem evalCaseIntrinsic_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (keyExpr branchesExpr : Pattern) :
    P s → P (evalCaseIntrinsic I s keyExpr branchesExpr).1 := by
  intro hP
  unfold evalCaseIntrinsic
  cases hKey : I.evalKeyValues s keyExpr with
  | mk sK keyOut =>
      have hK : P sK := by
        simpa [hKey] using H.evalKeyValues_preserves (s := s) (term := keyExpr) hKey hP
      cases hPairs : decodeCasePairs? branchesExpr with
      | none =>
          simpa [hKey, hPairs] using hK
      | some rawPairs =>
          let normalPairs := rawPairs.filter (fun kv => !isCaseDefaultPattern kv.1)
          let defaultPair? := rawPairs.find? (fun kv => isCaseDefaultPattern kv.1)
          let keys := if keyOut.isEmpty then [keyExpr] else keyOut
          have hFold : P ((keys.foldl (evalCaseKeyStep I defaultPair? normalPairs) (sK, [])).1) :=
            foldlState_preserves P (evalCaseKeyStep I defaultPair? normalPairs)
              (evalCaseKeyStep_preserves I P H defaultPair? normalPairs) keys (sK, []) hK
          simpa [normalPairs, defaultPair?, keys, hKey, hPairs]
            using hFold

private def evalFoldGeneratorStep (I : Interface σ) (aggVal g : Pattern)
    (accStep : σ × List Pattern) (accVal : Pattern) : σ × List Pattern :=
  let sessStep0 := accStep.1
  let nextAccRev := accStep.2
  let (sessStep1, callOut) := I.evalCallableApply sessStep0 aggVal [accVal, g]
  let nextVals := if callOut.isEmpty then [accVal] else callOut
  (sessStep1, nextVals.reverse ++ nextAccRev)

private theorem evalFoldGeneratorStep_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (aggVal g : Pattern) (accStep : σ × List Pattern) (accVal : Pattern) :
    P accStep.1 → P (evalFoldGeneratorStep I aggVal g accStep accVal).1 := by
  intro hP
  unfold evalFoldGeneratorStep
  exact H.evalCallableApply_preserves rfl hP

private def evalFoldGenerator (I : Interface σ) (aggVal : Pattern)
    (genVals : List Pattern) (sessFold : σ) (accVals : List Pattern) : σ × List Pattern :=
  match genVals with
  | [] => (sessFold, accVals)
  | g :: gs =>
      let (sessStep, nextRev) :=
        accVals.foldl (evalFoldGeneratorStep I aggVal g) (sessFold, [])
      evalFoldGenerator I aggVal gs sessStep nextRev.reverse

private theorem evalFoldGenerator_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (aggVal : Pattern) (genVals : List Pattern) (sessFold : σ) (accVals : List Pattern) :
    P sessFold → P (evalFoldGenerator I aggVal genVals sessFold accVals).1 := by
  intro hP
  induction genVals generalizing sessFold accVals with
  | nil =>
      simpa [evalFoldGenerator]
  | cons g gs ih =>
      have hStep :
          P ((accVals.foldl (evalFoldGeneratorStep I aggVal g) (sessFold, [])).1) :=
        foldlState_preserves P (evalFoldGeneratorStep I aggVal g)
          (evalFoldGeneratorStep_preserves I P H aggVal g) accVals (sessFold, []) hP
      simpa [evalFoldGenerator] using
        ih ((accVals.foldl (evalFoldGeneratorStep I aggVal g) (sessFold, [])).1)
          ((accVals.foldl (evalFoldGeneratorStep I aggVal g) (sessFold, [])).2.reverse) hStep

private def evalFoldallInitStep (I : Interface σ) (aggVal : Pattern)
    (genVals : List Pattern) (accInit : σ × List Pattern) (initVal : Pattern) : σ × List Pattern :=
  let sessInit := accInit.1
  let outInitRev := accInit.2
  let (sessFolded, foldedVals) := evalFoldGenerator I aggVal genVals sessInit [initVal]
  (sessFolded, foldedVals.reverse ++ outInitRev)

private theorem evalFoldallInitStep_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (aggVal : Pattern) (genVals : List Pattern)
    (accInit : σ × List Pattern) (initVal : Pattern) :
    P accInit.1 → P (evalFoldallInitStep I aggVal genVals accInit initVal).1 := by
  intro hP
  unfold evalFoldallInitStep
  exact evalFoldGenerator_preserves I P H aggVal genVals accInit.1 [initVal] hP

private def evalFoldallAggStep (I : Interface σ)
    (genVals initVals : List Pattern)
    (accOuter : σ × List Pattern) (aggVal : Pattern) : σ × List Pattern :=
  let sessOuter := accOuter.1
  let outOuter := accOuter.2
  let (sessAfterInit, foldedForAggRev) :=
    initVals.foldl (evalFoldallInitStep I aggVal genVals) (sessOuter, [])
  (sessAfterInit, foldedForAggRev ++ outOuter)

private theorem evalFoldallAggStep_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (genVals initVals : List Pattern)
    (accOuter : σ × List Pattern) (aggVal : Pattern) :
    P accOuter.1 → P (evalFoldallAggStep I genVals initVals accOuter aggVal).1 := by
  intro hP
  unfold evalFoldallAggStep
  exact foldlState_preserves P (evalFoldallInitStep I aggVal genVals)
    (evalFoldallInitStep_preserves I P H aggVal genVals) initVals (accOuter.1, []) hP

private def finalizeFoldall (st : σ × List Pattern) (initExpr : Pattern) : σ × List Pattern :=
  let out := st.2.reverse
  if out.isEmpty then
    (st.1, [initExpr])
  else
    (st.1, out)

private theorem finalizeFoldall_fst
    (st : σ × List Pattern) (initExpr : Pattern) :
    (finalizeFoldall st initExpr).1 = st.1 := by
  cases st with
  | mk s outRev =>
      unfold finalizeFoldall
      cases outRev with
      | nil =>
          simp
      | cons x xs =>
          simp

def evalFoldallIntrinsic (I : Interface σ) (s : σ)
    (aggExpr genExpr initExpr : Pattern) : σ × List Pattern :=
  let (sA, aggVals0) := I.eval s aggExpr
  let aggVals :=
    match aggExpr with
    | .apply _ [] => [aggExpr]
    | _ => if aggVals0.isEmpty then [aggExpr] else aggVals0
  let (sG, genVals0) := I.evalGeneratorValues sA genExpr
  let genVals := genVals0
  let (sI, initVals0) := I.eval sG initExpr
  let initVals := if initVals0.isEmpty then [initExpr] else initVals0
  finalizeFoldall (aggVals.foldl (evalFoldallAggStep I genVals initVals) (sI, [])) initExpr

theorem evalFoldallIntrinsic_fst
    (I : Interface σ) (s : σ) (aggExpr genExpr initExpr : Pattern) :
    (evalFoldallIntrinsic I s aggExpr genExpr initExpr).1 =
      (let (sA, aggVals0) := I.eval s aggExpr
       let aggVals :=
         match aggExpr with
         | .apply _ [] => [aggExpr]
         | _ => if aggVals0.isEmpty then [aggExpr] else aggVals0
       let (sG, genVals0) := I.evalGeneratorValues sA genExpr
       let genVals := genVals0
       let (sI, initVals0) := I.eval sG initExpr
       let initVals := if initVals0.isEmpty then [initExpr] else initVals0
       (aggVals.foldl (evalFoldallAggStep I genVals initVals) (sI, [])).1) := by
  unfold evalFoldallIntrinsic
  simp [finalizeFoldall_fst]

theorem evalFoldallIntrinsic_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (aggExpr genExpr initExpr : Pattern) :
    P s → P (evalFoldallIntrinsic I s aggExpr genExpr initExpr).1 := by
  intro hP
  unfold evalFoldallIntrinsic
  cases hAgg : I.eval s aggExpr with
  | mk sA aggVals0 =>
      have hA : P sA := by
        simpa [hAgg] using H.eval_preserves (s := s) (term := aggExpr) hAgg hP
      cases hGen : I.evalGeneratorValues sA genExpr with
      | mk sG genVals0 =>
          have hG : P sG := by
            simpa [hGen] using
              H.evalGeneratorValues_preserves (s := sA) (term := genExpr) hGen hA
          cases hInit : I.eval sG initExpr with
          | mk sI initVals0 =>
              have hI : P sI := by
                simpa [hInit] using H.eval_preserves (s := sG) (term := initExpr) hInit hG
              let aggVals :=
                match aggExpr with
                | .apply _ [] => [aggExpr]
                | _ => if aggVals0.isEmpty then [aggExpr] else aggVals0
              let genVals := genVals0
              let initVals := if initVals0.isEmpty then [initExpr] else initVals0
              let folded : σ × List Pattern :=
                aggVals.foldl (evalFoldallAggStep I genVals initVals) (sI, [])
              have hFold :
                  P folded.1 := by
                exact foldlState_preserves P (evalFoldallAggStep I genVals initVals)
                  (evalFoldallAggStep_preserves I P H genVals initVals) aggVals (sI, []) hI
              simpa [evalFoldallIntrinsic, hAgg, hGen, hInit, aggVals, genVals, initVals,
                folded, finalizeFoldall_fst] using hFold

private def evalCheckOneValueStep (I : Interface σ) (v : Pattern)
    (acc : σ × Bool) (checkVal : Pattern) : σ × Bool :=
  let sess0 := acc.1
  let okAcc := acc.2
  if okAcc then
    (sess0, true)
  else
    let (sess1, out) := I.evalCallableApply sess0 checkVal [v]
    let ok := out.any I.isTruthy
    (sess1, ok)

private theorem evalCheckOneValueStep_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (v : Pattern) (acc : σ × Bool) (checkVal : Pattern) :
    P acc.1 → P (evalCheckOneValueStep I v acc checkVal).1 := by
  intro hP
  unfold evalCheckOneValueStep
  by_cases hOk : acc.2
  · simp [hOk]
    exact hP
  · simp [hOk]
    exact H.evalCallableApply_preserves rfl hP

private def evalCheckOneValue (I : Interface σ)
    (checkVals : List Pattern) (sess : σ) (v : Pattern) : σ × Bool :=
  checkVals.foldl (evalCheckOneValueStep I v) (sess, false)

private theorem evalCheckOneValue_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (checkVals : List Pattern) (sess : σ) (v : Pattern) :
    P sess → P (evalCheckOneValue I checkVals sess v).1 := by
  intro hP
  unfold evalCheckOneValue
  exact foldlState_preserves P (evalCheckOneValueStep I v)
    (evalCheckOneValueStep_preserves I P H v) checkVals (sess, false) hP

private def evalCheckAll (I : Interface σ)
    (checkVals : List Pattern) (sess : σ) : List Pattern → σ × Bool
  | [] => (sess, true)
  | v :: rest =>
      let (sessV, passOne) := evalCheckOneValue I checkVals sess v
      if passOne then
        evalCheckAll I checkVals sessV rest
      else
        (sessV, false)

private theorem evalCheckAll_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (checkVals : List Pattern) (sess : σ) (vals : List Pattern) :
    P sess → P (evalCheckAll I checkVals sess vals).1 := by
  intro hP
  induction vals generalizing sess with
  | nil =>
      simpa [evalCheckAll]
  | cons v rest ih =>
      have hOne : P (evalCheckOneValue I checkVals sess v).1 :=
        evalCheckOneValue_preserves I P H checkVals sess v hP
      unfold evalCheckAll
      cases hCheck : evalCheckOneValue I checkVals sess v with
      | mk sessV passOne =>
          have hSessV : P sessV := by
            simpa [hCheck] using hOne
          by_cases hPass : passOne
          · simp [hPass]
            exact ih sessV hSessV
          · simp [hPass]
            exact hSessV

def evalForallIntrinsic (I : Interface σ) (s : σ)
    (genExpr checkExpr : Pattern) : σ × List Pattern :=
  let (sG, genVals) := I.evalGeneratorValues s genExpr
  let vals := genVals
  let (sC, checkVals0) := I.eval sG checkExpr
  let checkVals :=
    match checkExpr with
    | .apply _ [] => [checkExpr]
    | _ => if checkVals0.isEmpty then [checkExpr] else checkVals0
  let (sF, ok) := evalCheckAll I checkVals sC vals
  (sF, [I.patternOfBool ok])

theorem evalForallIntrinsic_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (genExpr checkExpr : Pattern) :
    P s → P (evalForallIntrinsic I s genExpr checkExpr).1 := by
  intro hP
  unfold evalForallIntrinsic
  cases hGen : I.evalGeneratorValues s genExpr with
  | mk sG genVals =>
      have hG : P sG := by
        simpa [hGen] using
          H.evalGeneratorValues_preserves (s := s) (term := genExpr) hGen hP
      cases hCheck : I.eval sG checkExpr with
      | mk sC checkVals0 =>
          have hC : P sC := by
            simpa [hCheck] using H.eval_preserves (s := sG) (term := checkExpr) hCheck hG
          let checkVals :=
            match checkExpr with
            | .apply _ [] => [checkExpr]
            | _ => if checkVals0.isEmpty then [checkExpr] else checkVals0
          have hAll : P (evalCheckAll I checkVals sC genVals).1 :=
            evalCheckAll_preserves I P H checkVals sC genVals hC
          simpa [checkVals, hGen, hCheck] using hAll

end Algorithms.MeTTa.Simple.Semantics.ControlFlow
