import Mettapedia.Languages.MeTTa.PureCertificateFragment
import Mettapedia.Languages.MeTTa.PureKernel.DefEq
import Mettapedia.Languages.MeTTa.PureKernel.Reduction
import Mettapedia.Languages.MeTTa.PureKernel.Substitution
import Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

/-!
# MeTTa-Pure CLI Support

A small executable evaluator and pretty surface parser for the current closed
Pure kernel fragment.

This module is intentionally narrow:

- closed terms only
- current Pure core only
- beta and sigma projection reduction
- pretty syntax and parsing for a small CLI subset

It does **not** claim ordinary-family or fixpoint reduction.
-/

namespace Mettapedia.Languages.MeTTa.PurePrototypeEval

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Confluence
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

/-! ## Executable evaluator -/

/-- One executable reduction step for the current Pure kernel fragment. -/
def stepCert? : (t : PureTm n) -> Option { u : PureTm n // Red t u }
  | .var _ => none
  | .u0 => none
  | .u1 => none
  | .unitTy => none
  | .unitMk => none
  | .boolTy => none
  | .boolFalse => none
  | .boolTrue => none
  | .natTy => none
  | .natZero => none
  | .natSucc k =>
      match stepCert? k with
      | some ⟨k', hk⟩ => some ⟨.natSucc k', .congNatSucc hk⟩
      | none => none
  | .pi A B =>
      match stepCert? A with
      | some ⟨A', hA⟩ => some ⟨.pi A' B, .congPiDom hA⟩
      | none =>
          match stepCert? B with
          | some ⟨B', hB⟩ => some ⟨.pi A B', .congPiCod hB⟩
          | none => none
  | .sigma A B =>
      match stepCert? A with
      | some ⟨A', hA⟩ => some ⟨.sigma A' B, .congSigmaDom hA⟩
      | none =>
          match stepCert? B with
          | some ⟨B', hB⟩ => some ⟨.sigma A B', .congSigmaCod hB⟩
          | none => none
  | .id A a b =>
      match stepCert? A with
      | some ⟨A', hA⟩ => some ⟨.id A' a b, .congIdTy hA⟩
      | none =>
          match stepCert? a with
          | some ⟨a', ha⟩ => some ⟨.id A a' b, .congIdLeft ha⟩
          | none =>
              match stepCert? b with
              | some ⟨b', hb⟩ => some ⟨.id A a b', .congIdRight hb⟩
              | none => none
  | .lam body =>
      match stepCert? body with
      | some ⟨body', hbody⟩ => some ⟨.lam body', .congLam hbody⟩
      | none => none
  | .app (.lam body) a =>
      some ⟨inst0 a body, .betaPi body a⟩
  | .app f a =>
      match stepCert? f with
      | some ⟨f', hf⟩ => some ⟨.app f' a, .congAppFun hf⟩
      | none =>
          match stepCert? a with
          | some ⟨a', ha⟩ => some ⟨.app f a', .congAppArg ha⟩
          | none => none
  | .pair a b =>
      match stepCert? a with
      | some ⟨a', ha⟩ => some ⟨.pair a' b, .congPairFst ha⟩
      | none =>
          match stepCert? b with
          | some ⟨b', hb⟩ => some ⟨.pair a b', .congPairSnd hb⟩
          | none => none
  | .fst (.pair a b) =>
      some ⟨a, .betaSigmaFst a b⟩
  | .fst p =>
      match stepCert? p with
      | some ⟨p', hp⟩ => some ⟨.fst p', .congFst hp⟩
      | none => none
  | .snd (.pair a b) =>
      some ⟨b, .betaSigmaSnd a b⟩
  | .snd p =>
      match stepCert? p with
      | some ⟨p', hp⟩ => some ⟨.snd p', .congSnd hp⟩
      | none => none
  | .refl a =>
      match stepCert? a with
      | some ⟨a', ha⟩ => some ⟨.refl a', .congRefl ha⟩
      | none => none
  | .unitRec motive unitCase .unitMk =>
      some ⟨unitCase, .betaUnitRec motive unitCase⟩
  | .unitRec motive unitCase scrutinee =>
      match stepCert? motive with
      | some ⟨motive', hmotive⟩ =>
          some ⟨.unitRec motive' unitCase scrutinee, .congUnitRecMotive hmotive⟩
      | none =>
          match stepCert? unitCase with
          | some ⟨unitCase', hcase⟩ =>
              some ⟨.unitRec motive unitCase' scrutinee, .congUnitRecCase hcase⟩
          | none =>
              match stepCert? scrutinee with
              | some ⟨scrutinee', hscrutinee⟩ =>
                  some ⟨.unitRec motive unitCase scrutinee', .congUnitRecScrutinee hscrutinee⟩
              | none => none
  | .boolRec motive falseCase trueCase .boolFalse =>
      some ⟨falseCase, .betaBoolRecFalse motive falseCase trueCase⟩
  | .boolRec motive falseCase trueCase .boolTrue =>
      some ⟨trueCase, .betaBoolRecTrue motive falseCase trueCase⟩
  | .boolRec motive falseCase trueCase scrutinee =>
      match stepCert? motive with
      | some ⟨motive', hmotive⟩ =>
          some ⟨.boolRec motive' falseCase trueCase scrutinee, .congBoolRecMotive hmotive⟩
      | none =>
          match stepCert? falseCase with
          | some ⟨falseCase', hfalse⟩ =>
              some ⟨.boolRec motive falseCase' trueCase scrutinee, .congBoolRecFalseCase hfalse⟩
          | none =>
              match stepCert? trueCase with
              | some ⟨trueCase', htrue⟩ =>
                  some ⟨.boolRec motive falseCase trueCase' scrutinee, .congBoolRecTrueCase htrue⟩
              | none =>
                  match stepCert? scrutinee with
                  | some ⟨scrutinee', hscrutinee⟩ =>
                      some ⟨.boolRec motive falseCase trueCase scrutinee', .congBoolRecScrutinee hscrutinee⟩
                  | none => none
  | .natRec motive zeroCase succCase .natZero =>
      some ⟨zeroCase, .betaNatRecZero motive zeroCase succCase⟩
  | .natRec motive zeroCase succCase (.natSucc k) =>
      some ⟨.app (.app succCase k) (.natRec motive zeroCase succCase k),
        .betaNatRecSucc motive zeroCase succCase k⟩
  | .natRec motive zeroCase succCase scrutinee =>
      match stepCert? motive with
      | some ⟨motive', hmotive⟩ =>
          some ⟨.natRec motive' zeroCase succCase scrutinee, .congNatRecMotive hmotive⟩
      | none =>
          match stepCert? zeroCase with
          | some ⟨zeroCase', hzero⟩ =>
              some ⟨.natRec motive zeroCase' succCase scrutinee, .congNatRecZeroCase hzero⟩
          | none =>
              match stepCert? succCase with
              | some ⟨succCase', hsucc⟩ =>
                  some ⟨.natRec motive zeroCase succCase' scrutinee, .congNatRecSuccCase hsucc⟩
              | none =>
                  match stepCert? scrutinee with
                  | some ⟨scrutinee', hscrutinee⟩ =>
                      some ⟨.natRec motive zeroCase succCase scrutinee', .congNatRecScrutinee hscrutinee⟩
                  | none => none

def evalPureStep? (t : PureTm n) : Option (PureTm n) :=
  (stepCert? t).map (·.1)

def evalPureFuel : Nat -> PureTm n -> PureTm n
  | 0, t => t
  | fuel + 1, t =>
      match stepCert? t with
      | some ⟨u, _⟩ => evalPureFuel fuel u
      | none => t

theorem evalPureFuel_redStar :
    ∀ (fuel : Nat) (t : PureTm n), RedStar t (evalPureFuel fuel t)
  | 0, t => RedStar.refl t
  | fuel + 1, t =>
      match hstep : stepCert? t with
      | none => by
          simp [evalPureFuel, hstep]
          exact RedStar.refl t
      | some step => by
          have htail : RedStar step.1 (evalPureFuel fuel step.1) :=
            evalPureFuel_redStar fuel step.1
          have hhead : RedStar t step.1 := red_to_redStar step.2
          simpa [evalPureFuel, hstep] using RedStar.trans hhead htail

theorem evalPureFuel_conv_cdev (fuel : Nat) (t : PureTm n) :
    Conv (evalPureFuel fuel t) (cdev t) := by
  have hFuel : Conv t (evalPureFuel fuel t) :=
    redStar_implies_conv (evalPureFuel_redStar fuel t)
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ hFuel)
    (Mettapedia.Languages.MeTTa.PureKernel.conv_to_cdev t)

structure ExecutablePureRun where
  input : SurfacePureTm 0
  fuel : Nat
  normalForm : PureTm 0
  theoryReduction : RedStar input.toPureTm normalForm

def runSurfacePure (fuel : Nat) (input : SurfacePureTm 0) : ExecutablePureRun :=
  { input := input
    fuel := fuel
    normalForm := evalPureFuel fuel input.toPureTm
    theoryReduction := evalPureFuel_redStar fuel input.toPureTm }

def ExecutablePureRun.artifact (run : ExecutablePureRun) : SharedArtifact :=
  ⟨quoteClosedTm run.normalForm⟩

theorem ExecutablePureRun.quoteAgreement (run : ExecutablePureRun) :
    run.artifact.pattern = quoteClosedTm run.normalForm := rfl

theorem ExecutablePureRun.profileBridge (run : ExecutablePureRun) :
    PureProfileTheoryStepStar
      (quoteClosedTm run.input.toPureTm)
      (quoteClosedTm run.normalForm) := by
  exact pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed run.theoryReduction

/-! ## Tiny pretty surface AST -/

inductive PrettyPureTm where
  | var (name : String)
  | u0
  | u1
  | unitTy
  | unitMk
  | boolTy
  | boolFalse
  | boolTrue
  | natTy
  | natZero
  | natSucc (k : PrettyPureTm)
  | pi (dom : PrettyPureTm) (binder : String) (body : PrettyPureTm)
  | sigma (dom : PrettyPureTm) (binder : String) (body : PrettyPureTm)
  | id (A : PrettyPureTm) (a : PrettyPureTm) (b : PrettyPureTm)
  | lam (binder : String) (body : PrettyPureTm)
  | app (f : PrettyPureTm) (a : PrettyPureTm)
  | pair (a : PrettyPureTm) (b : PrettyPureTm)
  | fst (p : PrettyPureTm)
  | snd (p : PrettyPureTm)
  | refl (a : PrettyPureTm)
  | unitRec (motive : PrettyPureTm) (unitCase : PrettyPureTm) (scrutinee : PrettyPureTm)
  | boolRec (motive : PrettyPureTm) (falseCase : PrettyPureTm) (trueCase : PrettyPureTm)
      (scrutinee : PrettyPureTm)
  | natRec (motive : PrettyPureTm) (zeroCase : PrettyPureTm) (succCase : PrettyPureTm)
      (scrutinee : PrettyPureTm)
deriving DecidableEq, Repr

inductive PrettyPureInput where
  | term (term : PrettyPureTm)
  | ann (term : PrettyPureTm) (type : PrettyPureTm)
deriving DecidableEq, Repr

structure ParsedPureInput where
  term : SurfacePureTm 0
  expectedType? : Option (SurfacePureTm 0)

def lookupName : (env : List String) -> String -> Option (Fin env.length)
  | [], _ => none
  | x :: xs, name =>
      if x = name then
        some 0
      else
        match lookupName xs name with
        | some i => some i.succ
        | none => none

def PrettyPureTm.toSurface : (env : List String) -> PrettyPureTm -> Except String (SurfacePureTm env.length)
  | env, .var name =>
      match lookupName env name with
      | some i => pure (.var i)
      | none => throw s!"unbound variable `{name}`"
  | _, .u0 => pure .u0
  | _, .u1 => pure .u1
  | _, .unitTy => pure .unitTy
  | _, .unitMk => pure .unitMk
  | _, .boolTy => pure .boolTy
  | _, .boolFalse => pure .boolFalse
  | _, .boolTrue => pure .boolTrue
  | _, .natTy => pure .natTy
  | _, .natZero => pure .natZero
  | env, .natSucc k => do
      pure (.natSucc (<- PrettyPureTm.toSurface env k))
  | env, .pi dom binder body => do
      let dom' <- PrettyPureTm.toSurface env dom
      let body' <- PrettyPureTm.toSurface (binder :: env) body
      pure (.pi dom' body')
  | env, .sigma dom binder body => do
      let dom' <- PrettyPureTm.toSurface env dom
      let body' <- PrettyPureTm.toSurface (binder :: env) body
      pure (.sigma dom' body')
  | env, .id A a b => do
      pure (.id
        (<- PrettyPureTm.toSurface env A)
        (<- PrettyPureTm.toSurface env a)
        (<- PrettyPureTm.toSurface env b))
  | env, .lam binder body => do
      let body' <- PrettyPureTm.toSurface (binder :: env) body
      pure (.lam body')
  | env, .app f a => do
      pure (.app
        (<- PrettyPureTm.toSurface env f)
        (<- PrettyPureTm.toSurface env a))
  | env, .pair a b => do
      pure (.pair
        (<- PrettyPureTm.toSurface env a)
        (<- PrettyPureTm.toSurface env b))
  | env, .fst p => do
      pure (.fst (<- PrettyPureTm.toSurface env p))
  | env, .snd p => do
      pure (.snd (<- PrettyPureTm.toSurface env p))
  | env, .refl a => do
      pure (.refl (<- PrettyPureTm.toSurface env a))
  | env, .unitRec motive unitCase scrutinee => do
      pure (.unitRec
        (<- PrettyPureTm.toSurface env motive)
        (<- PrettyPureTm.toSurface env unitCase)
        (<- PrettyPureTm.toSurface env scrutinee))
  | env, .boolRec motive falseCase trueCase scrutinee => do
      pure (.boolRec
        (<- PrettyPureTm.toSurface env motive)
        (<- PrettyPureTm.toSurface env falseCase)
        (<- PrettyPureTm.toSurface env trueCase)
        (<- PrettyPureTm.toSurface env scrutinee))
  | env, .natRec motive zeroCase succCase scrutinee => do
      pure (.natRec
        (<- PrettyPureTm.toSurface env motive)
        (<- PrettyPureTm.toSurface env zeroCase)
        (<- PrettyPureTm.toSurface env succCase)
        (<- PrettyPureTm.toSurface env scrutinee))

def parseClosedPrettyPureToSurface (term : PrettyPureTm) : Except String (SurfacePureTm 0) :=
  PrettyPureTm.toSurface [] term

def PrettyPureInput.toSurface : PrettyPureInput -> Except String ParsedPureInput
  | .term tm => do
      pure
        { term := <- parseClosedPrettyPureToSurface tm
          expectedType? := none }
  | .ann tm ty => do
      pure
        { term := <- parseClosedPrettyPureToSurface tm
          expectedType? := some (<- parseClosedPrettyPureToSurface ty) }

/-! ## Tiny tokenizer/parser -/

inductive Token where
  | lparen
  | rparen
  | lambda
  | arrow
  | ident (name : String)
deriving DecidableEq, Repr

private def flushIdent (chars : List Char) (tokensRev : List Token) : List Token :=
  if chars.isEmpty then
    tokensRev
  else
    Token.ident (String.ofList chars.reverse) :: tokensRev

private def isIdentChar (c : Char) : Bool :=
  !(c.isWhitespace || c = '(' || c = ')' || c = '\\')

private def tokenizeLoop :
    List Char -> List Char -> List Token -> Except String (List Token)
  | [], identRev, tokensRev =>
      pure (flushIdent identRev tokensRev).reverse
  | '=' :: '>' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.arrow :: flushIdent identRev tokensRev)
  | '(' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.lparen :: flushIdent identRev tokensRev)
  | ')' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.rparen :: flushIdent identRev tokensRev)
  | '\\' :: cs, identRev, tokensRev =>
      tokenizeLoop cs [] (Token.lambda :: flushIdent identRev tokensRev)
  | c :: cs, identRev, tokensRev =>
      if c.isWhitespace then
        tokenizeLoop cs [] (flushIdent identRev tokensRev)
      else if isIdentChar c then
        tokenizeLoop cs (c :: identRev) tokensRev
      else
        throw s!"unexpected character `{c}`"

private def stripLineComments (input : String) : String :=
  String.intercalate "\n" <|
    (input.splitOn "\n").map fun line =>
      match line.splitOn "--" with
      | [] => line
      | head :: _ => head

def tokenize (input : String) : Except String (List Token) :=
  tokenizeLoop (stripLineComments input).toList [] []

private def expectRParen : List Token -> Except String (List Token)
  | .rparen :: rest => pure rest
  | _ => throw "expected `)`"

mutual

partial def parsePrettyPure : List Token -> Except String (PrettyPureTm × List Token)
  | .ident "Type0" :: rest => pure (.u0, rest)
  | .ident "Type1" :: rest => pure (.u1, rest)
  | .ident "UnitTy" :: rest => pure (.unitTy, rest)
  | .ident "UnitMk" :: rest => pure (.unitMk, rest)
  | .ident "BoolTy" :: rest => pure (.boolTy, rest)
  | .ident "BoolFalse" :: rest => pure (.boolFalse, rest)
  | .ident "BoolTrue" :: rest => pure (.boolTrue, rest)
  | .ident "NatTy" :: rest => pure (.natTy, rest)
  | .ident "NatZero" :: rest => pure (.natZero, rest)
  | .ident name :: rest => pure (.var name, rest)
  | .lparen :: .ident "Type0" :: rest => do
      pure (.u0, <- expectRParen rest)
  | .lparen :: .ident "Type1" :: rest => do
      pure (.u1, <- expectRParen rest)
  | .lparen :: .ident "UnitTy" :: rest => do
      pure (.unitTy, <- expectRParen rest)
  | .lparen :: .ident "UnitMk" :: rest => do
      pure (.unitMk, <- expectRParen rest)
  | .lparen :: .ident "BoolTy" :: rest => do
      pure (.boolTy, <- expectRParen rest)
  | .lparen :: .ident "BoolFalse" :: rest => do
      pure (.boolFalse, <- expectRParen rest)
  | .lparen :: .ident "BoolTrue" :: rest => do
      pure (.boolTrue, <- expectRParen rest)
  | .lparen :: .ident "NatTy" :: rest => do
      pure (.natTy, <- expectRParen rest)
  | .lparen :: .ident "NatZero" :: rest => do
      pure (.natZero, <- expectRParen rest)
  | .lparen :: .ident "NatSucc" :: rest => do
      let (k, rest) <- parsePrettyPure rest
      pure (.natSucc k, <- expectRParen rest)
  | .lparen :: .ident "Pi" :: rest => do
      let (binder, dom, body, rest) <- parseDependentBinder rest
      pure (.pi dom binder body, <- expectRParen rest)
  | .lparen :: .ident "Sigma" :: rest => do
      let (binder, dom, body, rest) <- parseDependentBinder rest
      pure (.sigma dom binder body, <- expectRParen rest)
  | .lparen :: .ident "Id" :: rest => do
      let (A, rest) <- parsePrettyPure rest
      let (a, rest) <- parsePrettyPure rest
      let (b, rest) <- parsePrettyPure rest
      pure (.id A a b, <- expectRParen rest)
  | .lparen :: .lambda :: .ident binder :: .arrow :: rest => do
      let (body, rest) <- parsePrettyPure rest
      pure (.lam binder body, <- expectRParen rest)
  | .lparen :: .ident "lam" :: rest => do
      let (binder, body, rest) <- parseBinder rest
      pure (.lam binder body, <- expectRParen rest)
  | .lparen :: .ident "lambda" :: .ident binder :: rest => do
      let (body, rest) <- parsePrettyPure rest
      pure (.lam binder body, <- expectRParen rest)
  | .lparen :: .ident "app" :: rest => do
      let (f, rest) <- parsePrettyPure rest
      let (a, rest) <- parsePrettyPure rest
      pure (.app f a, <- expectRParen rest)
  | .lparen :: .ident "pair" :: rest => do
      let (a, rest) <- parsePrettyPure rest
      let (b, rest) <- parsePrettyPure rest
      pure (.pair a b, <- expectRParen rest)
  | .lparen :: .ident "fst" :: rest => do
      let (p, rest) <- parsePrettyPure rest
      pure (.fst p, <- expectRParen rest)
  | .lparen :: .ident "snd" :: rest => do
      let (p, rest) <- parsePrettyPure rest
      pure (.snd p, <- expectRParen rest)
  | .lparen :: .ident "refl" :: rest => do
      let (a, rest) <- parsePrettyPure rest
      pure (.refl a, <- expectRParen rest)
  | .lparen :: .ident "UnitRec" :: rest => do
      let (motive, rest) <- parsePrettyPure rest
      let (unitCase, rest) <- parsePrettyPure rest
      let (scrutinee, rest) <- parsePrettyPure rest
      pure (.unitRec motive unitCase scrutinee, <- expectRParen rest)
  | .lparen :: .ident "BoolRec" :: rest => do
      let (motive, rest) <- parsePrettyPure rest
      let (falseCase, rest) <- parsePrettyPure rest
      let (trueCase, rest) <- parsePrettyPure rest
      let (scrutinee, rest) <- parsePrettyPure rest
      pure (.boolRec motive falseCase trueCase scrutinee, <- expectRParen rest)
  | .lparen :: .ident "NatRec" :: rest => do
      let (motive, rest) <- parsePrettyPure rest
      let (zeroCase, rest) <- parsePrettyPure rest
      let (succCase, rest) <- parsePrettyPure rest
      let (scrutinee, rest) <- parsePrettyPure rest
      pure (.natRec motive zeroCase succCase scrutinee, <- expectRParen rest)
  | .lparen :: rest => do
      let (head, rest) <- parsePrettyPure rest
      parseApplicationTail head rest
  | _ => throw "expected Pure expression"

partial def parseBinder :
    List Token -> Except String (String × PrettyPureTm × List Token)
  | .lparen :: .lambda :: .ident binder :: .arrow :: rest => do
      let (body, rest) <- parsePrettyPure rest
      pure (binder, body, <- expectRParen rest)
  | .lparen :: .ident "lambda" :: .ident binder :: rest => do
      let (body, rest) <- parsePrettyPure rest
      pure (binder, body, <- expectRParen rest)
  | _ => throw "expected binder of the form `(lambda $x body)` or `(\\ x => body)`"

partial def parseDependentBinder :
    List Token -> Except String (String × PrettyPureTm × PrettyPureTm × List Token)
  | .lparen :: .ident binder :: .ident ":" :: rest => do
      let (dom, rest) <- parsePrettyPure rest
      let rest <- expectRParen rest
      let (body, rest) <- parsePrettyPure rest
      pure (binder, dom, body, rest)
  | rest => do
      let (dom, rest) <- parsePrettyPure rest
      let (binder, body, rest) <- parseBinder rest
      pure (binder, dom, body, rest)

partial def parseApplicationTail
    (head : PrettyPureTm) :
    List Token -> Except String (PrettyPureTm × List Token)
  | .rparen :: rest =>
      pure (head, rest)
  | tokens => do
      let (arg, rest) <- parsePrettyPure tokens
      parseApplicationTail (.app head arg) rest

end

private def parsePrettyPureInput :
    List Token -> Except String (PrettyPureInput × List Token)
  | .lparen :: .ident ":" :: rest => do
      let (term, rest) <- parsePrettyPure rest
      let (type, rest) <- parsePrettyPure rest
      pure (.ann term type, <- expectRParen rest)
  | tokens => do
      let (term, rest) <- parsePrettyPure tokens
      pure (.term term, rest)

def parseClosedPrettyPureInput (input : String) : Except String ParsedPureInput := do
  let tokens <- tokenize input
  let (prettyInput, rest) <- parsePrettyPureInput tokens
  if rest.isEmpty then
    prettyInput.toSurface
  else
    throw s!"unexpected trailing tokens: {reprStr rest}"

/-! ## Pretty printer -/

def binderName (depth : Nat) : String :=
  s!"$x{depth}"

def lookupBinderDisplay (env : List String) (i : Fin env.length) : String :=
  env.get i

def prettyWith : (env : List String) -> Nat -> PureTm env.length -> String
  | env, _, .var i => lookupBinderDisplay env i
  | _, _, .u0 => "(Type0)"
  | _, _, .u1 => "(Type1)"
  | _, _, .unitTy => "(UnitTy)"
  | _, _, .unitMk => "(UnitMk)"
  | _, _, .boolTy => "(BoolTy)"
  | _, _, .boolFalse => "(BoolFalse)"
  | _, _, .boolTrue => "(BoolTrue)"
  | _, _, .natTy => "(NatTy)"
  | _, _, .natZero => "(NatZero)"
  | env, depth, .natSucc k =>
      s!"(NatSucc {prettyWith env depth k})"
  | env, depth, .pi A B =>
      let x := binderName depth
      s!"(Pi ({x} : {prettyWith env depth A}) {prettyWith (x :: env) (depth + 1) B})"
  | env, depth, .sigma A B =>
      let x := binderName depth
      s!"(Sigma ({x} : {prettyWith env depth A}) {prettyWith (x :: env) (depth + 1) B})"
  | env, depth, .id A a b =>
      s!"(Id {prettyWith env depth A} {prettyWith env depth a} {prettyWith env depth b})"
  | env, depth, .lam body =>
      let x := binderName depth
      s!"(lambda {x} {prettyWith (x :: env) (depth + 1) body})"
  | env, depth, .app f a =>
      s!"({prettyWith env depth f} {prettyWith env depth a})"
  | env, depth, .pair a b =>
      s!"(pair {prettyWith env depth a} {prettyWith env depth b})"
  | env, depth, .fst p =>
      s!"(fst {prettyWith env depth p})"
  | env, depth, .snd p =>
      s!"(snd {prettyWith env depth p})"
  | env, depth, .refl a =>
      s!"(refl {prettyWith env depth a})"
  | env, depth, .unitRec motive unitCase scrutinee =>
      s!"(UnitRec {prettyWith env depth motive} {prettyWith env depth unitCase} {prettyWith env depth scrutinee})"
  | env, depth, .boolRec motive falseCase trueCase scrutinee =>
      s!"(BoolRec {prettyWith env depth motive} {prettyWith env depth falseCase} {prettyWith env depth trueCase} {prettyWith env depth scrutinee})"
  | env, depth, .natRec motive zeroCase succCase scrutinee =>
      s!"(NatRec {prettyWith env depth motive} {prettyWith env depth zeroCase} {prettyWith env depth succCase} {prettyWith env depth scrutinee})"

def prettyClosed (t : PureTm 0) : String :=
  prettyWith [] 0 t

/-! ## CLI support -/

def defaultFuel : Nat := 64

private def formatArtifactPattern (artifact : SharedArtifact) : String :=
  s!"{repr artifact.pattern}"

private def formatEvalSummary : List String :=
  [ "proof: artifact-agreement=ok"
  , "proof: profile-bridge=ok"
  ]

def runPureEvalFile (path : System.FilePath) (fuel : Nat := defaultFuel) : IO UInt32 := do
  let input <- IO.FS.readFile path
  match parseClosedPrettyPureInput input with
  | .error err =>
      IO.eprintln s!"pure-eval parse error in {path}: {err}"
      pure 1
  | .ok parsed =>
      let run := runSurfacePure fuel parsed.term
      IO.println s!"input: {prettyClosed parsed.term.toPureTm}"
      match parsed.expectedType? with
      | some expectedType =>
          IO.println s!"annotation: {prettyClosed expectedType.toPureTm}"
      | none =>
          pure ()
      IO.println s!"normalized: {prettyClosed run.normalForm}"
      IO.println s!"artifact: {formatArtifactPattern run.artifact}"
      for line in formatEvalSummary do
        IO.println line
      pure 0

end Mettapedia.Languages.MeTTa.PurePrototypeEval
