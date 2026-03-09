import Mettapedia.Languages.MeTTa.RuntimeExec
import Mettapedia.Languages.MeTTa.Core.Bridge
import Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Languages.MeTTa.PureRuntimeFrontier

/-!
# Elaborated MeTTa-Core

Proof-of-concept classification layer sitting above `PureKernel` and
`RuntimeExec`.

The point of this module is not to redefine either branch. It makes explicit the
missing middle layer suggested by the current architecture:

- one surface MeTTa node
- one elaborated classification
- multiple certified downstream views

Current regions:

- `pureKernelRegion`: trusted typed fragment routed to `PureKernel`
- `runtimeExecRegion`: effectful/runtime fragment routed to `RuntimeSpec` and
  an execution/query seam
- `oracleRegion`: grounded/FFI/oracle boundary kept explicit
- `metaRegion`: proof/elaboration-time reflection layer
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.DialectProfile
open Mettapedia.Languages.MeTTa.RuntimeSpec
open Mettapedia.Languages.MeTTa.RuntimeExec
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.Core.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The first explicit region split for elaborated MeTTa-Core. -/
inductive ElaboratedRegion where
  | pureKernelRegion
  | runtimeExecRegion
  | oracleRegion
  | metaRegion
deriving DecidableEq, Repr

/-- Shared artifact substrate used by both proof and runtime views. -/
structure SharedArtifact where
  pattern : Pattern

/-- Runtime-side lowering target. This is intentionally smaller than "all
runtime semantics": it only records the current theoremic seams. -/
inductive RuntimeLowering where
  | exec (surface : MeTTaRuntimeExecSurface)
  | query (surface : MeTTaRuntimeQuerySurface)
  | auditOnly

def RuntimeLowering.backendName : RuntimeLowering → String
  | RuntimeLowering.exec surface => surface.backendName
  | RuntimeLowering.query surface => surface.backendName
  | RuntimeLowering.auditOnly => "audit-only"

/-- Current overlap classification between the proof side and the runtime side.

`artifactOnly` is the present honest overlap for closed Pure terms: they share a
quoted MeTTa artifact and WM-facing semantic landing, but they do not yet lower
through the direct `R_exec₀` source-rule bridge.

`directExec` is reserved for future fragments that genuinely elaborate to both a
trusted proof target and the current theoremic runtime execution seam. -/
inductive OverlapClass where
  | artifactOnly
  | directExec (surface : MeTTaRuntimeExecSurface)

def OverlapClass.name : OverlapClass → String
  | .artifactOnly => "artifact-only"
  | .directExec surface => surface.backendName

/-- Small binder-aware surface syntax for the first real pure fragment above
`PureKernel`.

This mirrors the trusted Pure syntax closely on purpose: the immediate goal is
to make the first dual-view certificate real, not to invent a second kernel. -/
inductive SurfacePureTm : Nat → Type where
  | var : Fin n → SurfacePureTm n
  | u0 : SurfacePureTm n
  | u1 : SurfacePureTm n
  | pi : SurfacePureTm n → SurfacePureTm (n + 1) → SurfacePureTm n
  | sigma : SurfacePureTm n → SurfacePureTm (n + 1) → SurfacePureTm n
  | id : SurfacePureTm n → SurfacePureTm n → SurfacePureTm n → SurfacePureTm n
  | lam : SurfacePureTm (n + 1) → SurfacePureTm n
  | app : SurfacePureTm n → SurfacePureTm n → SurfacePureTm n
  | pair : SurfacePureTm n → SurfacePureTm n → SurfacePureTm n
  | fst : SurfacePureTm n → SurfacePureTm n
  | snd : SurfacePureTm n → SurfacePureTm n
  | refl : SurfacePureTm n → SurfacePureTm n
deriving DecidableEq, Repr

namespace SurfacePureTm

def toPureTm : SurfacePureTm n → PureTm n
  | .var i => .var i
  | .u0 => .u0
  | .u1 => .u1
  | .pi A B => .pi (toPureTm A) (toPureTm B)
  | .sigma A B => .sigma (toPureTm A) (toPureTm B)
  | .id A a b => .id (toPureTm A) (toPureTm a) (toPureTm b)
  | .lam b => .lam (toPureTm b)
  | .app f a => .app (toPureTm f) (toPureTm a)
  | .pair a b => .pair (toPureTm a) (toPureTm b)
  | .fst p => .fst (toPureTm p)
  | .snd p => .snd (toPureTm p)
  | .refl a => .refl (toPureTm a)

def toPatternWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : SurfacePureTm n → Pattern
  | .var i => .fvar (ρ i)
  | .u0 => Mettapedia.Languages.MeTTa.Pure.Core.u0
  | .u1 => Mettapedia.Languages.MeTTa.Pure.Core.u1
  | .pi A B =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Pure.Core.mkPi (toPatternWith ν k ρ A)
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) B))
  | .sigma A B =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Pure.Core.mkSigma (toPatternWith ν k ρ A)
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) B))
  | .id A a b =>
      Mettapedia.Languages.MeTTa.Pure.Core.mkId
        (toPatternWith ν k ρ A) (toPatternWith ν k ρ a) (toPatternWith ν k ρ b)
  | .lam b =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Pure.Core.mkLam
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) b))
  | .app f a =>
      Mettapedia.Languages.MeTTa.Pure.Core.mkApp (toPatternWith ν k ρ f) (toPatternWith ν k ρ a)
  | .pair a b =>
      Mettapedia.Languages.MeTTa.Pure.Core.mkPair (toPatternWith ν k ρ a) (toPatternWith ν k ρ b)
  | .fst p => Mettapedia.Languages.MeTTa.Pure.Core.mkFst (toPatternWith ν k ρ p)
  | .snd p => Mettapedia.Languages.MeTTa.Pure.Core.mkSnd (toPatternWith ν k ρ p)
  | .refl a => Mettapedia.Languages.MeTTa.Pure.Core.mkRefl (toPatternWith ν k ρ a)

def toPattern (ρ : QuoteEnv n) (t : SurfacePureTm n) : Pattern :=
  toPatternWith defaultBinderName 0 ρ t

def toClosedPattern (t : SurfacePureTm 0) : Pattern :=
  toPattern emptyEnv t

theorem toPatternWith_eq_quoteTmWith
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    ∀ t : SurfacePureTm n, toPatternWith ν k ρ t = quoteTmWith ν k ρ (toPureTm t)
  | .var i => rfl
  | .u0 => rfl
  | .u1 => rfl
  | .pi A B => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .sigma A B => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .id A a b => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .lam b => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .app f a => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .pair a b => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .fst p => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .snd p => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .refl a => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]

theorem toPattern_eq_quoteTm (ρ : QuoteEnv n) (t : SurfacePureTm n) :
    toPattern ρ t = quoteTm ρ (toPureTm t) := by
  simpa [toPattern, quoteTm] using toPatternWith_eq_quoteTmWith defaultBinderName 0 ρ t

theorem toClosedPattern_eq_quoteClosedTm (t : SurfacePureTm 0) :
    toClosedPattern t = quoteClosedTm (toPureTm t) := by
  simpa [toClosedPattern, quoteClosedTm] using toPattern_eq_quoteTm emptyEnv t

end SurfacePureTm

abbrev CoreAtom := Mettapedia.Languages.MeTTa.Core.Atom
abbrev CoreAtomspace := Mettapedia.Languages.MeTTa.Core.Atomspace
abbrev CoreGroundedValue := Mettapedia.Languages.MeTTa.Core.GroundedValue

/-- Small typed MeTTa-Core surface fragment whose atoms already have a shared
artifact view through `Core.Bridge.atomToPattern`.

This is intentionally weaker than a direct PureKernel compilation target:
- positive example: symbolic atoms, variables, and expression constructors that
  already admit a `Pattern` view
- negative example: grounded atoms do not currently admit such a view and are
  excluded from this fragment
-/
structure SurfaceCoreTypedAtom where
  space : CoreAtomspace
  atom : CoreAtom
  ty : CoreAtom
  typed : Mettapedia.Languages.MeTTa.Core.HasType space atom ty
  pattern : Pattern
  pattern_eq : atomToPattern atom = some pattern

namespace SurfaceCoreTypedAtom

def toArtifact (surface : SurfaceCoreTypedAtom) : SharedArtifact :=
  ⟨surface.pattern⟩

def ofSymbol (space : CoreAtomspace) (s : String) : SurfaceCoreTypedAtom :=
  { space := space
    atom := .symbol s
    ty := .symbol "Symbol"
    typed := Mettapedia.Languages.MeTTa.Core.HasType.intrinsicSymbol s
    pattern := .apply s []
    pattern_eq := by simp [atomToPattern] }

def ofVariable (space : CoreAtomspace) (v : String) : SurfaceCoreTypedAtom :=
  { space := space
    atom := .var v
    ty := .symbol "Variable"
    typed := Mettapedia.Languages.MeTTa.Core.HasType.intrinsicVariable v
    pattern := .fvar v
    pattern_eq := by simp [atomToPattern] }

def ofAnnotated
    (space : CoreAtomspace)
    (atom ty : CoreAtom)
    (pattern : Pattern)
    (hpattern : atomToPattern atom = some pattern)
    (hannot : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom ty ∈ space.atoms) :
    SurfaceCoreTypedAtom :=
  { space := space
    atom := atom
    ty := ty
    typed := Mettapedia.Languages.MeTTa.Core.annotation_gives_type space atom ty hannot
    pattern := pattern
    pattern_eq := hpattern }

theorem grounded_atom_has_no_pattern (g : CoreGroundedValue) :
    atomToPattern (.grounded g : CoreAtom) = none := by
  simp [atomToPattern]

theorem symbol_pattern_example (space : CoreAtomspace) (s : String) :
    (ofSymbol space s).pattern = .apply s [] := rfl

theorem variable_pattern_example (space : CoreAtomspace) (v : String) :
    (ofVariable space v).pattern = .fvar v := rfl

/-- Soundness of the existing decidable type checker for the first elaborated
typed-atom fragment. This keeps the elaborator honest: checked typed atoms are
turned into proof-carrying typed atoms, not postulated ones. -/
theorem checkType_true_implies_hasType
    (space : CoreAtomspace) (atom ty : CoreAtom) :
    Mettapedia.Languages.MeTTa.Core.checkType space atom ty = true →
      Mettapedia.Languages.MeTTa.Core.HasType space atom ty := by
  intro h
  cases ty with
  | var v =>
      have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.var v) ∈ space.atoms := by
        simpa [Mettapedia.Languages.MeTTa.Core.checkType, Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.var v) hmem
  | grounded g =>
      have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.grounded g) ∈ space.atoms := by
        simpa [Mettapedia.Languages.MeTTa.Core.checkType, Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.grounded g) hmem
  | expression es =>
      have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.expression es) ∈ space.atoms := by
        simpa [Mettapedia.Languages.MeTTa.Core.checkType, Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.expression es) hmem
  | symbol s =>
      by_cases hSymbol : s = "Symbol"
      · subst hSymbol
        cases atom with
        | var v =>
            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
        | symbol s =>
            exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicSymbol s
        | grounded g =>
            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
        | expression es =>
            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
      · by_cases hVariable : s = "Variable"
        · subst hVariable
          cases atom with
          | var v =>
              exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicVariable v
          | symbol s =>
              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
          | grounded g =>
              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
          | expression es =>
              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
        · by_cases hGrounded : s = "Grounded"
          · subst hGrounded
            cases atom with
            | var v =>
                simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
            | symbol s =>
                simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
            | grounded g =>
                exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicGrounded g
            | expression es =>
                simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
          · by_cases hExpression : s = "Expression"
            · subst hExpression
              cases atom with
              | var v =>
                  simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
              | symbol s =>
                  simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
              | grounded g =>
                  simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
              | expression es =>
                  exact Mettapedia.Languages.MeTTa.Core.HasType.intrinsicExpression es
            · by_cases hAtom : s = "Atom"
              · subst hAtom
                exact Mettapedia.Languages.MeTTa.Core.hasTypeAtom space atom
              · by_cases hInt : s = "Int"
                · subst hInt
                  cases atom with
                  | var v =>
                      simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  | symbol s =>
                      simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  | grounded g =>
                      cases g with
                      | int n =>
                          exact Mettapedia.Languages.MeTTa.Core.HasType.groundedInt n
                      | string s =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | bool b =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | custom typeName data =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  | expression es =>
                      simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                · by_cases hString : s = "String"
                  · subst hString
                    cases atom with
                    | var v =>
                        simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    | symbol s =>
                        simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    | grounded g =>
                        cases g with
                        | int n =>
                            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                        | string s =>
                            exact Mettapedia.Languages.MeTTa.Core.HasType.groundedString s
                        | bool b =>
                            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                        | custom typeName data =>
                            simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    | expression es =>
                        simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                  · by_cases hBool : s = "Bool"
                    · subst hBool
                      cases atom with
                      | var v =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | symbol s =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | grounded g =>
                          cases g with
                          | int n =>
                              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                          | string s =>
                              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                          | bool b =>
                              exact Mettapedia.Languages.MeTTa.Core.HasType.groundedBool b
                          | custom typeName data =>
                              simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                      | expression es =>
                          simp [Mettapedia.Languages.MeTTa.Core.checkType] at h
                    · have hmem : Mettapedia.Languages.MeTTa.Core.typeAnnotation atom (.symbol s) ∈ space.atoms := by
                        simpa [Mettapedia.Languages.MeTTa.Core.checkType, hSymbol, hVariable, hGrounded,
                          hExpression, hAtom, hInt, hString, hBool,
                          Mettapedia.Languages.MeTTa.Core.Atomspace.contains] using h
                      exact Mettapedia.Languages.MeTTa.Core.HasType.annotated atom (.symbol s) hmem

end SurfaceCoreTypedAtom

/-- Certificate for the trusted Pure branch. -/
structure PureCertificate where
  term : PureTm 0
  artifact : SharedArtifact
  artifact_eq : artifact.pattern = quoteClosedTm term
  abcSurface : PureClosedABCSurface := defaultPureClosedABCSurface

/-- First real overlap certificate for a shared pure surface fragment.

This is the first nontrivial "both views at once" object:
- one binder-aware surface term,
- one trusted PureKernel term,
- one shared MeTTa artifact,
- and a proof that the two downstream views agree. -/
structure SharedPureOverlapCertificate where
  surface : SurfacePureTm 0
  pure : PureCertificate
  overlapClass : OverlapClass
  pure_eq : pure.term = surface.toPureTm
  artifact_eq_surface : pure.artifact.pattern = surface.toClosedPattern
  artifact_eq_pure : pure.artifact.pattern = quoteClosedTm pure.term

def SharedPureOverlapCertificate.backendName (_ : SharedPureOverlapCertificate) : String :=
  "PureKernel+Artifact"

def certifySurfacePure (surface : SurfacePureTm 0) : SharedPureOverlapCertificate :=
  let pure : PureCertificate := {
    term := surface.toPureTm
    artifact := ⟨surface.toClosedPattern⟩
    artifact_eq := by simpa using surface.toClosedPattern_eq_quoteClosedTm
  }
  {
    surface := surface
    pure := pure
    overlapClass := OverlapClass.artifactOnly
    pure_eq := rfl
    artifact_eq_surface := rfl
    artifact_eq_pure := pure.artifact_eq
  }

/-- Certificate for the first typed MeTTa-Core fragment above both the proof and
runtime branches.

This still records an `artifactOnly` overlap: the fragment has a typed
proof-oriented contract and a shared MeTTa artifact view, but it is not yet a
direct `R_exec₀` execution certificate. -/
structure CoreTypedCertificate where
  surface : SurfaceCoreTypedAtom
  overlapClass : OverlapClass
  artifact : SharedArtifact
  artifact_eq : artifact.pattern = surface.pattern

def CoreTypedCertificate.backendName (_ : CoreTypedCertificate) : String :=
  "CoreTypes+Artifact"

def certifySurfaceCoreTypedAtom (surface : SurfaceCoreTypedAtom) : CoreTypedCertificate :=
  { surface := surface
    overlapClass := OverlapClass.artifactOnly
    artifact := surface.toArtifact
    artifact_eq := rfl }

namespace SurfaceCoreTypedAtom

/-- First real elaborator for typed MeTTa-Core atoms:

- it checks the type with `checkType`
- it reuses the existing `atomToPattern` bridge for the shared artifact
- it produces an honest certificate only when both views exist -/
def elaborateCheckedCoreTypedAtom?
    (space : CoreAtomspace) (atom ty : CoreAtom) : Option CoreTypedCertificate := do
  match hct : Mettapedia.Languages.MeTTa.Core.checkType space atom ty with
  | false => none
  | true =>
      match hpat : atomToPattern atom with
      | none => none
      | some pattern =>
          let surface : SurfaceCoreTypedAtom :=
            { space := space
              atom := atom
              ty := ty
              typed := checkType_true_implies_hasType space atom ty hct
              pattern := pattern
              pattern_eq := hpat }
          pure (certifySurfaceCoreTypedAtom surface)

end SurfaceCoreTypedAtom

/-- Certificate for the runtime branch. -/
structure RuntimeCertificate where
  dialect : MeTTaDialectProfile
  spec : MeTTaRuntimeSpec
  lowering : RuntimeLowering
  artifact : SharedArtifact
  dialect_eq : spec.dialect = dialect

/-- Certificate for grounded / FFI / oracle calls. -/
structure OracleCertificate where
  dialect : MeTTaDialectProfile
  opName : String
  resultDescriptor : String
  args : List Pattern
  artifact : SharedArtifact

/-- Certificate for elaboration-time / proof-time metaprogramming nodes. -/
structure MetaCertificate where
  description : String
  artifact : SharedArtifact

/-- The first explicit elaborated-core object. -/
inductive ElaboratedNode where
  | pureNode (cert : PureCertificate)
  | coreTypedNode (cert : CoreTypedCertificate)
  | runtimeNode (cert : RuntimeCertificate)
  | oracleNode (cert : OracleCertificate)
  | metaNode (cert : MetaCertificate)

def ElaboratedNode.region : ElaboratedNode → ElaboratedRegion
  | ElaboratedNode.pureNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.coreTypedNode _ => ElaboratedRegion.pureKernelRegion
  | ElaboratedNode.runtimeNode _ => ElaboratedRegion.runtimeExecRegion
  | ElaboratedNode.oracleNode _ => ElaboratedRegion.oracleRegion
  | ElaboratedNode.metaNode _ => ElaboratedRegion.metaRegion

def ElaboratedNode.artifact : ElaboratedNode → SharedArtifact
  | ElaboratedNode.pureNode cert => cert.artifact
  | ElaboratedNode.coreTypedNode cert => cert.artifact
  | ElaboratedNode.runtimeNode cert => cert.artifact
  | ElaboratedNode.oracleNode cert => cert.artifact
  | ElaboratedNode.metaNode cert => cert.artifact

/-- Tiny surface language for the first elaboration proof-of-concept.

This is deliberately smaller than full MeTTa. The purpose is to make the
downstream split explicit before committing to a richer elaborator.
-/
inductive SurfaceNode where
  | surfacePureClosed (term : SurfacePureTm 0)
  | coreTypedAtom (surface : SurfaceCoreTypedAtom)
  | heRuntimeRule (pattern : Pattern)
  | heRuntimeQuery (pattern : Pattern)
  | pettaRuntimeRule (pattern : Pattern)
  | pettaRuntimeQuery (pattern : Pattern)
  | fullLegacyRuntime (pattern : Pattern)
  | oracleCall
      (dialect : MeTTaDialectProfile)
      (opName : String)
      (resultDescriptor : String)
      (args : List Pattern)
  | metaQuoted (description : String) (pattern : Pattern)

/-- Proof-of-concept elaborator from a tiny surface language into the first
explicit elaborated MeTTa-Core. -/
noncomputable def elaborate : SurfaceNode → ElaboratedNode
  | SurfaceNode.surfacePureClosed term =>
      ElaboratedNode.pureNode (certifySurfacePure term).pure
  | SurfaceNode.coreTypedAtom surface =>
      ElaboratedNode.coreTypedNode (certifySurfaceCoreTypedAtom surface)
  | SurfaceNode.heRuntimeRule pattern =>
      ElaboratedNode.runtimeNode {
        dialect := heDialectProfile
        spec := heRuntimeSpec
        lowering := RuntimeLowering.exec morkRuntimeExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.heRuntimeQuery pattern =>
      ElaboratedNode.runtimeNode {
        dialect := heDialectProfile
        spec := heRuntimeSpec
        lowering := RuntimeLowering.query morkRuntimeQueryExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.pettaRuntimeRule pattern =>
      ElaboratedNode.runtimeNode {
        dialect := pettaDialectProfile
        spec := pettaRuntimeSpec
        lowering := RuntimeLowering.exec morkRuntimeExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.pettaRuntimeQuery pattern =>
      ElaboratedNode.runtimeNode {
        dialect := pettaDialectProfile
        spec := pettaRuntimeSpec
        lowering := RuntimeLowering.query morkRuntimeQueryExec0
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.fullLegacyRuntime pattern =>
      ElaboratedNode.runtimeNode {
        dialect := fullLegacyDialectProfile
        spec := fullLegacyRuntimeSpec
        lowering := RuntimeLowering.auditOnly
        artifact := ⟨pattern⟩
        dialect_eq := rfl
      }
  | SurfaceNode.oracleCall dialect opName resultDescriptor args =>
      ElaboratedNode.oracleNode {
        dialect := dialect
        opName := opName
        resultDescriptor := resultDescriptor
        args := args
        artifact := ⟨Pattern.apply opName args⟩
      }
  | SurfaceNode.metaQuoted description pattern =>
      ElaboratedNode.metaNode {
        description := description
        artifact := ⟨pattern⟩
      }

theorem elaborate_surfacePureClosed_region (term : SurfacePureTm 0) :
    ElaboratedNode.region (elaborate (SurfaceNode.surfacePureClosed term)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_coreTypedAtom_region (surface : SurfaceCoreTypedAtom) :
    ElaboratedNode.region (elaborate (SurfaceNode.coreTypedAtom surface)) =
      ElaboratedRegion.pureKernelRegion := rfl

theorem elaborate_heRuntimeRule_region (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SurfaceNode.heRuntimeRule pattern)) =
      ElaboratedRegion.runtimeExecRegion := rfl

theorem elaborate_pettaRuntimeQuery_region (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SurfaceNode.pettaRuntimeQuery pattern)) =
      ElaboratedRegion.runtimeExecRegion := rfl

theorem elaborate_oracleCall_region
    (dialect : MeTTaDialectProfile) (opName resultDescriptor : String)
    (args : List Pattern) :
    ElaboratedNode.region
        (elaborate (SurfaceNode.oracleCall dialect opName resultDescriptor args)) =
      ElaboratedRegion.oracleRegion := rfl

theorem elaborate_metaQuoted_region
    (description : String) (pattern : Pattern) :
    ElaboratedNode.region (elaborate (SurfaceNode.metaQuoted description pattern)) =
      ElaboratedRegion.metaRegion := rfl

theorem elaborate_surfacePureClosed_artifact
    (term : SurfacePureTm 0) :
    (ElaboratedNode.artifact (elaborate (SurfaceNode.surfacePureClosed term))).pattern =
      term.toClosedPattern := rfl

theorem elaborate_coreTypedAtom_artifact
    (surface : SurfaceCoreTypedAtom) :
    (ElaboratedNode.artifact (elaborate (SurfaceNode.coreTypedAtom surface))).pattern =
      surface.pattern := rfl

theorem elaborate_surfacePureClosed_term
    (term : SurfacePureTm 0) :
    match elaborate (SurfaceNode.surfacePureClosed term) with
    | ElaboratedNode.pureNode cert => cert.term = term.toPureTm
    | _ => False := by
  simp [elaborate, certifySurfacePure]

theorem elaborate_surfacePureClosed_quoteAgreement
    (term : SurfacePureTm 0) :
    (ElaboratedNode.artifact (elaborate (SurfaceNode.surfacePureClosed term))).pattern =
      quoteClosedTm term.toPureTm := by
  simpa [elaborate, certifySurfacePure] using term.toClosedPattern_eq_quoteClosedTm

theorem elaborate_surfacePureClosed_abcSurface
    (term : SurfacePureTm 0) :
    match elaborate (SurfaceNode.surfacePureClosed term) with
    | ElaboratedNode.pureNode cert => cert.abcSurface = defaultPureClosedABCSurface
    | _ => False := by
  simp [elaborate]

theorem elaborate_heRuntimeRule_backend
    (pattern : Pattern) :
    match elaborate (SurfaceNode.heRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "MORK/MM2"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName, morkRuntimeExec0_backendName]

theorem elaborate_pettaRuntimeRule_backend
    (pattern : Pattern) :
    match elaborate (SurfaceNode.pettaRuntimeRule pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "MORK/MM2"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName, morkRuntimeExec0_backendName]

theorem elaborate_fullLegacyRuntime_auditOnly
    (pattern : Pattern) :
    match elaborate (SurfaceNode.fullLegacyRuntime pattern) with
    | ElaboratedNode.runtimeNode cert =>
        RuntimeLowering.backendName cert.lowering = "audit-only"
    | _ => False := by
  simp [elaborate, RuntimeLowering.backendName]

/-- Proof-of-concept certificate that a closed Pure term already has a shared
artifact view at the MeTTaIL substrate. -/
noncomputable def pureArtifactCertificate (term : SurfacePureTm 0) : SharedArtifact :=
  ElaboratedNode.artifact (elaborate (SurfaceNode.surfacePureClosed term))

theorem certifySurfacePure_backendName (term : SurfacePureTm 0) :
    (certifySurfacePure term).backendName = "PureKernel+Artifact" := rfl

theorem certifySurfaceCoreTypedAtom_backendName (surface : SurfaceCoreTypedAtom) :
    (certifySurfaceCoreTypedAtom surface).backendName = "CoreTypes+Artifact" := rfl

theorem certifySurfacePure_overlapClass (term : SurfacePureTm 0) :
    (certifySurfacePure term).overlapClass = OverlapClass.artifactOnly := rfl

theorem certifySurfaceCoreTypedAtom_overlapClass (surface : SurfaceCoreTypedAtom) :
    (certifySurfaceCoreTypedAtom surface).overlapClass = OverlapClass.artifactOnly := rfl

theorem certifySurfacePure_overlapName (term : SurfacePureTm 0) :
    OverlapClass.name (certifySurfacePure term).overlapClass = "artifact-only" := rfl

theorem certifySurfaceCoreTypedAtom_overlapName (surface : SurfaceCoreTypedAtom) :
    OverlapClass.name (certifySurfaceCoreTypedAtom surface).overlapClass = "artifact-only" := rfl

/-- Current Pure overlap is already real, but it is not direct runtime source
execution. The frontier theorem lives at the language/rewrite level; this
certificate-level theorem records the same conclusion in elaborated-core terms. -/
theorem surfacePureClosed_overlap_is_not_directExec
    (term : SurfacePureTm 0) :
    (certifySurfacePure term).overlapClass ≠ OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifySurfacePure]

theorem surfaceCoreTypedAtom_overlap_is_not_directExec
    (surface : SurfaceCoreTypedAtom) :
    (certifySurfaceCoreTypedAtom surface).overlapClass ≠
      OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifySurfaceCoreTypedAtom]

/-- Language-level summary imported from `PureRuntimeFrontier`: the current
`mettaPure` rewrite system still does not satisfy the direct `R_exec₀`
source-rule bridge hypotheses. -/
theorem mettaPure_language_frontier_is_not_directExec0
    (r : RewriteRule)
    (hr : r ∈ Mettapedia.Languages.MeTTa.Pure.Core.mettaPure.rewrites) :
    ¬ ∃ x, r.left = .fvar x ∧
      Mettapedia.Languages.ProcessCalculi.MORK.morkTranslatable r.right = true :=
  PureRuntimeFrontier.no_mettaPure_rewrite_fits_direct_runtimeExec0_source_bridge r hr

/-- Proof-of-concept certificate that HE runtime rules and PeTTa runtime rules
already target the same theoremic backend seam, even though they remain
different dialects. -/
theorem runtimeBackendAgreement
    (hePattern pettaPattern : Pattern) :
    match elaborate (SurfaceNode.heRuntimeRule hePattern),
          elaborate (SurfaceNode.pettaRuntimeRule pettaPattern) with
    | ElaboratedNode.runtimeNode heCert, ElaboratedNode.runtimeNode pettaCert =>
        RuntimeLowering.backendName heCert.lowering =
          RuntimeLowering.backendName pettaCert.lowering
    | _, _ => False := by
  simp [elaborate, RuntimeLowering.backendName]

end Mettapedia.Languages.MeTTa.ElaboratedCore
