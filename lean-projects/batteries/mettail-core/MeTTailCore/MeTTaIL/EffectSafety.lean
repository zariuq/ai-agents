import MeTTailCore.MeTTaIL.Syntax
import MeTTailCore.MeTTaIL.TransitionSpec
import MeTTailCore.MeTTaIL.TransitionPlan

namespace MeTTailCore.MeTTaIL.EffectSafety

open MeTTailCore.MeTTaIL.Syntax

/--
Coarse effect classes for premise relations and transition effects.

The order is intentional:

`pureStructural < readOnlyLookup < nondeterministicReadOnly < writesState < oracleIO`

This lets us compute a conservative overall effect with `join`.
-/
inductive EffectClass where
  | pureStructural
  | readOnlyLookup
  | nondeterministicReadOnly
  | writesState
  | oracleIO
deriving Repr, DecidableEq, BEq

/--
Memoization shape matters:

- `scalar` caches one deterministic result
- `outcomeSet` caches the full read-only outcome set
-/
inductive MemoShape where
  | scalar
  | outcomeSet
deriving Repr, DecidableEq, BEq

def EffectClass.rank : EffectClass → Nat
  | .pureStructural => 0
  | .readOnlyLookup => 1
  | .nondeterministicReadOnly => 2
  | .writesState => 3
  | .oracleIO => 4

def EffectClass.join (a b : EffectClass) : EffectClass :=
  if a.rank <= b.rank then b else a

theorem EffectClass.join_comm (a b : EffectClass) : a.join b = b.join a := by
  cases a <;> cases b <;> decide

theorem EffectClass.join_assoc (a b c : EffectClass) :
    a.join (b.join c) = (a.join b).join c := by
  cases a <;> cases b <;> cases c <;> decide

theorem EffectClass.join_pureStructural_left (a : EffectClass) :
    EffectClass.pureStructural.join a = a := by
  cases a <;> decide

theorem EffectClass.join_pureStructural_right (a : EffectClass) :
    a.join EffectClass.pureStructural = a := by
  cases a <;> decide

def EffectClass.supportsMemoShape : EffectClass → MemoShape → Bool
  | .pureStructural, .scalar => true
  | .pureStructural, .outcomeSet => true
  | .readOnlyLookup, .scalar => true
  | .readOnlyLookup, .outcomeSet => true
  | .nondeterministicReadOnly, .scalar => false
  | .nondeterministicReadOnly, .outcomeSet => true
  | .writesState, _ => false
  | .oracleIO, _ => false

abbrev RelationEffectProfile := String → Option EffectClass
abbrev TransitionEffectProfile := String → Option EffectClass

def Premise.effectClass? (profile : RelationEffectProfile) : Premise → Option EffectClass
  | .freshness _ => some .pureStructural
  | .congruence _ _ => some .pureStructural
  | .relationQuery rel _ => profile rel

def premisesEffectClass? (profile : RelationEffectProfile) (premises : List Premise) :
    Option EffectClass :=
  premises.foldl
    (fun acc prem =>
      match acc, Premise.effectClass? profile prem with
      | some cls, some next => some (cls.join next)
      | _, _ => none)
    (some .pureStructural)

structure RuleEffectSummary where
  premiseEffect : EffectClass
  transitionEffect : EffectClass
deriving Repr, DecidableEq, BEq

def RuleEffectSummary.overallEffect (summary : RuleEffectSummary) : EffectClass :=
  summary.premiseEffect.join summary.transitionEffect

def RuleEffectSummary.supportsMemoShape (summary : RuleEffectSummary) (shape : MemoShape) : Bool :=
  summary.overallEffect.supportsMemoShape shape

def RuleEffectSummary.memoizationContractAdmissible (summary : RuleEffectSummary) : Bool :=
  summary.supportsMemoShape .outcomeSet

def summarizeRewriteRuleWithTransition?
    (relationProfile : RelationEffectProfile)
    (transitionEffect : EffectClass)
    (rule : RewriteRule) : Option RuleEffectSummary := do
  let premiseEffect ← premisesEffectClass? relationProfile rule.premises
  pure { premiseEffect := premiseEffect, transitionEffect := transitionEffect }

def MeTTailCore.MeTTaIL.TransitionSpec.TransitionSemanticKey.effectClass?
    (profile : TransitionEffectProfile)
    (key : MeTTailCore.MeTTaIL.TransitionSpec.TransitionSemanticKey) : Option EffectClass :=
  profile key.effectKind

def MeTTailCore.MeTTaIL.TransitionPlan.TransitionSemanticKey.effectClass?
    (profile : TransitionEffectProfile)
    (key : MeTTailCore.MeTTaIL.TransitionPlan.TransitionSemanticKey) : Option EffectClass :=
  profile key.effectKind

def MeTTailCore.MeTTaIL.TransitionSpec.TransitionSemanticKey.declaresMemoizationSafe
    (key : MeTTailCore.MeTTaIL.TransitionSpec.TransitionSemanticKey) : Bool :=
  key.contracts.contains MeTTailCore.MeTTaIL.TransitionSpec.TransitionContract.memoizationSafe

def MeTTailCore.MeTTaIL.TransitionPlan.TransitionSemanticKey.declaresMemoizationSafe
    (key : MeTTailCore.MeTTaIL.TransitionPlan.TransitionSemanticKey) : Bool :=
  key.contracts.contains MeTTailCore.MeTTaIL.TransitionPlan.TransitionContract.memoizationSafe

def summarizeRewriteRuleWithSpecKey?
    (relationProfile : RelationEffectProfile)
    (transitionProfile : TransitionEffectProfile)
    (rule : RewriteRule)
    (key : MeTTailCore.MeTTaIL.TransitionSpec.TransitionSemanticKey) :
    Option RuleEffectSummary := do
  let transitionEffect ←
    MeTTailCore.MeTTaIL.TransitionSpec.TransitionSemanticKey.effectClass?
      transitionProfile
      key
  summarizeRewriteRuleWithTransition? relationProfile transitionEffect rule

def summarizeRewriteRuleWithPlanKey?
    (relationProfile : RelationEffectProfile)
    (transitionProfile : TransitionEffectProfile)
    (rule : RewriteRule)
    (key : MeTTailCore.MeTTaIL.TransitionPlan.TransitionSemanticKey) :
    Option RuleEffectSummary := do
  let transitionEffect ←
    MeTTailCore.MeTTaIL.TransitionPlan.TransitionSemanticKey.effectClass?
      transitionProfile
      key
  summarizeRewriteRuleWithTransition? relationProfile transitionEffect rule

theorem pureStructural_scalar_memo_safe :
    EffectClass.pureStructural.supportsMemoShape .scalar = true := by
  decide

theorem pureStructural_outcome_memo_safe :
    EffectClass.pureStructural.supportsMemoShape .outcomeSet = true := by
  decide

theorem readOnlyLookup_scalar_memo_safe :
    EffectClass.readOnlyLookup.supportsMemoShape .scalar = true := by
  decide

theorem nondeterministicReadOnly_not_scalar_memo_safe :
    EffectClass.nondeterministicReadOnly.supportsMemoShape .scalar = false := by
  decide

theorem nondeterministicReadOnly_outcome_memo_safe :
    EffectClass.nondeterministicReadOnly.supportsMemoShape .outcomeSet = true := by
  decide

theorem writesState_not_outcome_memo_safe :
    EffectClass.writesState.supportsMemoShape .outcomeSet = false := by
  decide

theorem oracleIO_not_outcome_memo_safe :
    EffectClass.oracleIO.supportsMemoShape .outcomeSet = false := by
  decide

end MeTTailCore.MeTTaIL.EffectSafety
