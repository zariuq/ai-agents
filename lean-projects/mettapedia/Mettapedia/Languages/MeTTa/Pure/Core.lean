import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory

/-!
# MeTTa-Pure: Intensional Dependent Type Theory as a LanguageDef

MeTTa-Pure is the **initial intensional dependent kernel** for MeTTa,
defined as a `LanguageDef` instance in the MeTTa-IL framework. It
provides:

- **Π-types** (dependent function types)
- **Σ-types** (dependent pair types)
- **Id-types** (identity / propositional equality)
- **Two Russell-style universes**: `U0 : U1`
- **Core β-reductions**: for Π (App∘Lam), Σ-fst (Fst∘Pair), Σ-snd (Snd∘Pair),
  and starter ordinary-family recursors for `Unit`, `Bool`, `Nat`
- **No equations** (intensional — no extensional axioms)

Being a `LanguageDef`, it automatically receives:
- OSLF behavioral types via `langOSLF`
- Galois connection `◇ ⊣ □` via `langGalois`
- Constructor category via `constructorCategory`

## Architecture

```
MeTTa-Pure   = initial intensional dependent kernel
MeTTa-Core   = initial admissible MeTTa home (Pure + Runtime + Bridge + OSLF)
MeTTa-Full-* = conservative extension profiles (HE, PeTTa, PathMap, ...)
```

MeTTa-Pure is NOT Turing-complete (that belongs to the runtime in MeTTa-Core).
It is total, decidable, and strongly normalizing in its type-level fragment.

## References

- Adjedj et al., "Martin-Löf à la Coq" (2023, arXiv:2310.06376)
- Weirich, "pi-forall" (2022, arXiv:2207.02129)
- Meredith & Stay, MeTTa-IL specification
-/

namespace Mettapedia.Languages.MeTTa.Pure.Core

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory

/-! ## Language Definition -/

/-- MeTTa-Pure: a small intensional dependent type theory.

    - **Sorts**: `["Tm", "Ctx"]`
    - **Tm constructors**: `U0`, `U1`, `Pi`, `Sigma`, `Id`, `Lam`, `App`,
      `Pair`, `Fst`, `Snd`, `Refl`, `UnitTy`, `UnitMk`, `BoolTy`,
      `BoolFalse`, `BoolTrue`, `NatTy`, `NatZero`, `NatSucc`, `UnitRec`,
      `BoolRec`, `NatRec`
    - **Ctx constructors**: `CtxEmpty`, `CtxExtend`
    - **Reductions**: BetaPi, BetaSigmaFst, BetaSigmaSnd, BetaUnitRec,
      BetaBoolRecFalse, BetaBoolRecTrue, BetaNatRecZero, BetaNatRecSucc -/
def mettaPure : LanguageDef := {
  name := "MeTTaPure",
  types := ["Tm", "Ctx"],
  terms := [
    -- U0 : Tm  (universe 0)
    { label := "U0", category := "Tm", params := [],
      syntaxPattern := [.terminal "U0"] },
    -- U1 : Tm  (universe 1)
    { label := "U1", category := "Tm", params := [],
      syntaxPattern := [.terminal "U1"] },
    -- Pi(A, ^B) : Tm  (dependent function type)
    { label := "Pi", category := "Tm",
      params := [.simple "A" (.base "Tm"),
                 .abstraction "B" (.arrow (.base "Tm") (.base "Tm"))],
      syntaxPattern := [.terminal "Pi", .terminal "(",
                        .nonTerminal "A", .terminal ",",
                        .nonTerminal "B", .terminal ")"] },
    -- Sigma(A, ^B) : Tm  (dependent pair type)
    { label := "Sigma", category := "Tm",
      params := [.simple "A" (.base "Tm"),
                 .abstraction "B" (.arrow (.base "Tm") (.base "Tm"))],
      syntaxPattern := [.terminal "Sigma", .terminal "(",
                        .nonTerminal "A", .terminal ",",
                        .nonTerminal "B", .terminal ")"] },
    -- Id(A, a, b) : Tm  (identity type)
    { label := "Id", category := "Tm",
      params := [.simple "A" (.base "Tm"),
                 .simple "a" (.base "Tm"),
                 .simple "b" (.base "Tm")],
      syntaxPattern := [.terminal "Id", .terminal "(",
                        .nonTerminal "A", .terminal ",",
                        .nonTerminal "a", .terminal ",",
                        .nonTerminal "b", .terminal ")"] },
    -- Lam(^body) : Tm  (lambda abstraction)
    { label := "Lam", category := "Tm",
      params := [.abstraction "body" (.arrow (.base "Tm") (.base "Tm"))],
      syntaxPattern := [.terminal "lam", .terminal ".", .nonTerminal "body"] },
    -- App(f, a) : Tm  (application)
    { label := "App", category := "Tm",
      params := [.simple "f" (.base "Tm"), .simple "a" (.base "Tm")],
      syntaxPattern := [.nonTerminal "f", .nonTerminal "a"] },
    -- Pair(a, b) : Tm  (dependent pair introduction)
    { label := "Pair", category := "Tm",
      params := [.simple "a" (.base "Tm"), .simple "b" (.base "Tm")],
      syntaxPattern := [.terminal "(", .nonTerminal "a", .terminal ",",
                        .nonTerminal "b", .terminal ")"] },
    -- Fst(p) : Tm  (first projection)
    { label := "Fst", category := "Tm",
      params := [.simple "p" (.base "Tm")],
      syntaxPattern := [.terminal "fst", .nonTerminal "p"] },
    -- Snd(p) : Tm  (second projection)
    { label := "Snd", category := "Tm",
      params := [.simple "p" (.base "Tm")],
      syntaxPattern := [.terminal "snd", .nonTerminal "p"] },
    -- Refl(a) : Tm  (reflexivity proof)
    { label := "Refl", category := "Tm",
      params := [.simple "a" (.base "Tm")],
      syntaxPattern := [.terminal "refl", .nonTerminal "a"] },
    -- UnitTy : Tm
    { label := "UnitTy", category := "Tm", params := [],
      syntaxPattern := [.terminal "UnitTy"] },
    -- UnitMk : Tm
    { label := "UnitMk", category := "Tm", params := [],
      syntaxPattern := [.terminal "UnitMk"] },
    -- BoolTy : Tm
    { label := "BoolTy", category := "Tm", params := [],
      syntaxPattern := [.terminal "BoolTy"] },
    -- BoolFalse : Tm
    { label := "BoolFalse", category := "Tm", params := [],
      syntaxPattern := [.terminal "BoolFalse"] },
    -- BoolTrue : Tm
    { label := "BoolTrue", category := "Tm", params := [],
      syntaxPattern := [.terminal "BoolTrue"] },
    -- NatTy : Tm
    { label := "NatTy", category := "Tm", params := [],
      syntaxPattern := [.terminal "NatTy"] },
    -- NatZero : Tm
    { label := "NatZero", category := "Tm", params := [],
      syntaxPattern := [.terminal "NatZero"] },
    -- NatSucc(k) : Tm
    { label := "NatSucc", category := "Tm",
      params := [.simple "k" (.base "Tm")],
      syntaxPattern := [.terminal "NatSucc", .terminal "(", .nonTerminal "k", .terminal ")"] },
    -- UnitRec(motive, unitCase, scrutinee) : Tm
    { label := "UnitRec", category := "Tm",
      params := [.simple "motive" (.base "Tm"),
                 .simple "unitCase" (.base "Tm"),
                 .simple "scrutinee" (.base "Tm")],
      syntaxPattern := [.terminal "UnitRec", .terminal "(",
                        .nonTerminal "motive", .terminal ",",
                        .nonTerminal "unitCase", .terminal ",",
                        .nonTerminal "scrutinee", .terminal ")"] },
    -- BoolRec(motive, falseCase, trueCase, scrutinee) : Tm
    { label := "BoolRec", category := "Tm",
      params := [.simple "motive" (.base "Tm"),
                 .simple "falseCase" (.base "Tm"),
                 .simple "trueCase" (.base "Tm"),
                 .simple "scrutinee" (.base "Tm")],
      syntaxPattern := [.terminal "BoolRec", .terminal "(",
                        .nonTerminal "motive", .terminal ",",
                        .nonTerminal "falseCase", .terminal ",",
                        .nonTerminal "trueCase", .terminal ",",
                        .nonTerminal "scrutinee", .terminal ")"] },
    -- NatRec(motive, zeroCase, succCase, scrutinee) : Tm
    { label := "NatRec", category := "Tm",
      params := [.simple "motive" (.base "Tm"),
                 .simple "zeroCase" (.base "Tm"),
                 .simple "succCase" (.base "Tm"),
                 .simple "scrutinee" (.base "Tm")],
      syntaxPattern := [.terminal "NatRec", .terminal "(",
                        .nonTerminal "motive", .terminal ",",
                        .nonTerminal "zeroCase", .terminal ",",
                        .nonTerminal "succCase", .terminal ",",
                        .nonTerminal "scrutinee", .terminal ")"] },
    -- CtxEmpty : Ctx  (empty context)
    { label := "CtxEmpty", category := "Ctx", params := [],
      syntaxPattern := [.terminal "[]"] },
    -- CtxExtend(G, A) : Ctx  (context extension)
    { label := "CtxExtend", category := "Ctx",
      params := [.simple "G" (.base "Ctx"), .simple "A" (.base "Tm")],
      syntaxPattern := [.nonTerminal "G", .terminal ",", .nonTerminal "A"] }
  ],
  equations := [],
  rewrites := [
    -- BetaPi: App(Lam(^body), a) ~> body[a/x]
    { name := "BetaPi",
      typeContext := [("body", .base "Tm"), ("a", .base "Tm")],
      premises := [],
      left := .apply "App" [.apply "Lam" [.lambda (.fvar "body")], .fvar "a"],
      right := .subst (.fvar "body") (.fvar "a") },
    -- BetaSigmaFst: Fst(Pair(a, b)) ~> a
    { name := "BetaSigmaFst",
      typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
      premises := [],
      left := .apply "Fst" [.apply "Pair" [.fvar "a", .fvar "b"]],
      right := .fvar "a" },
    -- BetaSigmaSnd: Snd(Pair(a, b)) ~> b
    { name := "BetaSigmaSnd",
      typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
      premises := [],
      left := .apply "Snd" [.apply "Pair" [.fvar "a", .fvar "b"]],
      right := .fvar "b" },
    -- BetaUnitRec: UnitRec(motive, unitCase, UnitMk) ~> unitCase
    { name := "BetaUnitRec",
      typeContext := [("motive", .base "Tm"), ("unitCase", .base "Tm")],
      premises := [],
      left := .apply "UnitRec" [.fvar "motive", .fvar "unitCase", .apply "UnitMk" []],
      right := .fvar "unitCase" },
    -- BetaBoolRecFalse: BoolRec(motive, falseCase, trueCase, BoolFalse) ~> falseCase
    { name := "BetaBoolRecFalse",
      typeContext := [("motive", .base "Tm"), ("falseCase", .base "Tm"), ("trueCase", .base "Tm")],
      premises := [],
      left := .apply "BoolRec"
        [.fvar "motive", .fvar "falseCase", .fvar "trueCase", .apply "BoolFalse" []],
      right := .fvar "falseCase" },
    -- BetaBoolRecTrue: BoolRec(motive, falseCase, trueCase, BoolTrue) ~> trueCase
    { name := "BetaBoolRecTrue",
      typeContext := [("motive", .base "Tm"), ("falseCase", .base "Tm"), ("trueCase", .base "Tm")],
      premises := [],
      left := .apply "BoolRec"
        [.fvar "motive", .fvar "falseCase", .fvar "trueCase", .apply "BoolTrue" []],
      right := .fvar "trueCase" },
    -- BetaNatRecZero: NatRec(motive, zeroCase, succCase, NatZero) ~> zeroCase
    { name := "BetaNatRecZero",
      typeContext := [("motive", .base "Tm"), ("zeroCase", .base "Tm"), ("succCase", .base "Tm")],
      premises := [],
      left := .apply "NatRec"
        [.fvar "motive", .fvar "zeroCase", .fvar "succCase", .apply "NatZero" []],
      right := .fvar "zeroCase" },
    -- BetaNatRecSucc: NatRec(motive, zeroCase, succCase, NatSucc(k))
    --   ~> App(App(succCase, k), NatRec(motive, zeroCase, succCase, k))
    { name := "BetaNatRecSucc",
      typeContext := [("motive", .base "Tm"), ("zeroCase", .base "Tm"), ("succCase", .base "Tm"), ("k", .base "Tm")],
      premises := [],
      left := .apply "NatRec"
        [.fvar "motive", .fvar "zeroCase", .fvar "succCase", .apply "NatSucc" [.fvar "k"]],
      right := .apply "App"
        [.apply "App" [.fvar "succCase", .fvar "k"],
         .apply "NatRec" [.fvar "motive", .fvar "zeroCase", .fvar "succCase", .fvar "k"]] }
  ]
}

/-! ## Helper Constructors -/

/-- Universe 0. -/
def u0 : Pattern := .apply "U0" []

/-- Universe 1. -/
def u1 : Pattern := .apply "U1" []

/-- Dependent function type `Π(x : A). B`. The body `B` should contain
    `.bvar 0` for references to the bound variable. -/
def mkPi (A B : Pattern) : Pattern := .apply "Pi" [A, .lambda B]

/-- Dependent pair type `Σ(x : A). B`. -/
def mkSigma (A B : Pattern) : Pattern := .apply "Sigma" [A, .lambda B]

/-- Identity type `Id_A(a, b)`. -/
def mkId (A a b : Pattern) : Pattern := .apply "Id" [A, a, b]

/-- Lambda abstraction `λx. body`. -/
def mkLam (body : Pattern) : Pattern := .apply "Lam" [.lambda body]

/-- Application `f a`. -/
def mkApp (f a : Pattern) : Pattern := .apply "App" [f, a]

/-- Dependent pair `(a, b)`. -/
def mkPair (a b : Pattern) : Pattern := .apply "Pair" [a, b]

/-- First projection `fst p`. -/
def mkFst (p : Pattern) : Pattern := .apply "Fst" [p]

/-- Second projection `snd p`. -/
def mkSnd (p : Pattern) : Pattern := .apply "Snd" [p]

/-- Reflexivity proof `refl a`. -/
def mkRefl (a : Pattern) : Pattern := .apply "Refl" [a]

/-- Unit type. -/
def mkUnitTy : Pattern := .apply "UnitTy" []

/-- Unit constructor. -/
def mkUnitMk : Pattern := .apply "UnitMk" []

/-- Bool type. -/
def mkBoolTy : Pattern := .apply "BoolTy" []

/-- False constructor. -/
def mkBoolFalse : Pattern := .apply "BoolFalse" []

/-- True constructor. -/
def mkBoolTrue : Pattern := .apply "BoolTrue" []

/-- Nat type. -/
def mkNatTy : Pattern := .apply "NatTy" []

/-- Zero constructor. -/
def mkNatZero : Pattern := .apply "NatZero" []

/-- Successor constructor. -/
def mkNatSucc (k : Pattern) : Pattern := .apply "NatSucc" [k]

/-- Unit recursor. -/
def mkUnitRec (motive unitCase scrutinee : Pattern) : Pattern :=
  .apply "UnitRec" [motive, unitCase, scrutinee]

/-- Bool recursor. -/
def mkBoolRec (motive falseCase trueCase scrutinee : Pattern) : Pattern :=
  .apply "BoolRec" [motive, falseCase, trueCase, scrutinee]

/-- Nat recursor. -/
def mkNatRec (motive zeroCase succCase scrutinee : Pattern) : Pattern :=
  .apply "NatRec" [motive, zeroCase, succCase, scrutinee]

/-- Empty context. -/
def mkCtxEmpty : Pattern := .apply "CtxEmpty" []

/-- Context extension `Γ, A`. -/
def mkCtxExtend (G A : Pattern) : Pattern := .apply "CtxExtend" [G, A]

/-! ## OSLF Pipeline Instantiation -/

/-- The OSLF type system for MeTTa-Pure (Tm is the process sort).
    Galois connection ◇ ⊣ □ is proven automatically. -/
def mettaPureOSLF := langOSLF mettaPure "Tm"

/-- The Galois connection for MeTTa-Pure: ◇ ⊣ □. -/
theorem mettaPureGalois :
    GaloisConnection (langDiamond mettaPure) (langBox mettaPure) :=
  langGalois mettaPure

/-! ## Constructor Category Instantiation -/

/-- The Tm sort in MeTTa-Pure's constructor category. -/
def pureTm : LangSort mettaPure := ⟨"Tm", by decide⟩

/-- The Ctx sort in MeTTa-Pure's constructor category. -/
def pureCtx : LangSort mettaPure := ⟨"Ctx", by decide⟩

/-- MeTTa-Pure has exactly 2 sorts. -/
theorem mettaPure_types : mettaPure.types = ["Tm", "Ctx"] := rfl

/-- MeTTa-Pure currently has 8 rewrite rules. -/
theorem mettaPure_rewrites_length : mettaPure.rewrites.length = 8 := by decide

/-- MeTTa-Pure has no equations (intensional). -/
theorem mettaPure_no_equations : mettaPure.equations = [] := rfl

/-! ## Executable Demos -/

#eval!
  let identity := mkLam (.bvar 0)      -- λx. x
  let a := .fvar "a"                   -- free variable a
  let redex := mkApp identity a        -- (λx. x) a
  let result := rewriteWithContext mettaPure redex
  (redex, result)

#eval!
  let a := .fvar "a"
  let b := .fvar "b"
  let redex := mkFst (mkPair a b)      -- fst (a, b)
  let result := rewriteWithContext mettaPure redex
  (redex, result)

#eval!
  let a := .fvar "a"
  let b := .fvar "b"
  let redex := mkSnd (mkPair a b)      -- snd (a, b)
  let result := rewriteWithContext mettaPure redex
  (redex, result)

end Mettapedia.Languages.MeTTa.Pure.Core
