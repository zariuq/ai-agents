import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration
import Mettapedia.UniversalAI.TimeBoundedAIXI.CodingBits

/-!
# Chapter 7: Proof-system-style checkers (non-oracle interface)

`ProofEnumerationOracle` provides a baseline “complete proof checker” by *baking the target predicate*
`P` into the decoder.  For Chapter 7’s proof-enumeration semantics, it is often more convenient to
model a *syntactic* proof system:

- certificates encode a statement `a : α` together with a proof object `pr`,
- a (computable) verifier `verify t a pr : Bool` checks the proof object,
- soundness/completeness are stated as assumptions relating `verify` to the semantic predicate `P`.

This module packages that interface and turns it into a `CompleteProofCheckerFamily` compatible with
the rest of the Chapter 7 development.
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI

universe u v

open scoped Classical

/-! ## Encodable proof systems -/

/-- A proof-system interface for predicates `P t a`, where certificates are bitstrings encoding
`(a, pr)` for an explicit proof object `pr`, and verification is performed by a Boolean procedure. -/
structure EncodableProofSystemFamily {α : Type u} [Encodable α] (P : ℕ → α → Prop) where
  /-- Proof objects carried by certificates. -/
  Proof : Type v
  /-- Proof objects must be encodable to/from certificates. -/
  [encProof : Encodable Proof]
  /-- Verifier for proof objects. -/
  verify : ℕ → α → Proof → Bool
  /-- Soundness: verified proofs establish the target predicate. -/
  sound : ∀ {t a pr}, verify t a pr = true → P t a
  /-- Completeness: any true statement admits some verifiable proof object. -/
  complete : ∀ t a, P t a → ∃ pr, verify t a pr = true

attribute [instance] EncodableProofSystemFamily.encProof

/-! ## Sound-only proof systems -/

/-- A sound (not necessarily complete) proof-system interface for predicates `P t a`.

This is often the right “MVP” abstraction for Chapter 7: the proof-enumeration semantics only
needs certificates for the specific near-optimal programs you care about, not global completeness
for *all* true statements. -/
structure EncodableSoundProofSystemFamily {α : Type u} [Encodable α] (P : ℕ → α → Prop) where
  /-- Proof objects carried by certificates. -/
  Proof : Type v
  /-- Proof objects must be encodable to/from certificates. -/
  [encProof : Encodable Proof]
  /-- Verifier for proof objects. -/
  verify : ℕ → α → Proof → Bool
  /-- Soundness: verified proofs establish the target predicate. -/
  sound : ∀ {t a pr}, verify t a pr = true → P t a

attribute [instance] EncodableSoundProofSystemFamily.encProof

namespace EncodableProofSystemFamily

variable {α : Type u} [Encodable α] {P : ℕ → α → Prop}

/-- Forget completeness. -/
def toSound (sys : EncodableProofSystemFamily (α := α) P) : EncodableSoundProofSystemFamily (α := α) P :=
  { Proof := sys.Proof
    verify := sys.verify
    sound := sys.sound }

/-- A trivial (noncomputable) proof system for any predicate `P`, using classical decidability:
`verify t a _` returns `true` exactly when `P t a` holds. -/
noncomputable def ofDecidable (P : ℕ → α → Prop) : EncodableProofSystemFamily (α := α) P := by
  classical
  refine
    { Proof := Unit
      verify := fun t a _pr => decide (P t a)
      sound := ?_
      complete := ?_ }
  · intro t a _pr h
    exact of_decide_eq_true h
  · intro t a ha
    refine ⟨(), ?_⟩
    exact decide_eq_true ha

/-- Decode a certificate (bitstring) to a statement `a : α`, accepting it if the bundled proof
object passes `verify`. -/
def decode (sys : EncodableProofSystemFamily (α := α) P) (t : ℕ) : ProofDecoder α :=
  fun bits =>
    match Coding.decodeEncodableBits (α := α × sys.Proof) bits with
    | some ap =>
        let a := ap.1
        let pr := ap.2
        if sys.verify t a pr then some a else none
    | none => none

theorem sound_decode (sys : EncodableProofSystemFamily (α := α) P) {t : ℕ} {bits : List Bool} {a : α}
    (hdec : sys.decode t bits = some a) : P t a := by
  classical
  unfold EncodableProofSystemFamily.decode at hdec
  cases hbits : Coding.decodeEncodableBits (α := α × sys.Proof) bits with
  | none =>
      simp [hbits] at hdec
  | some ap =>
      cases hverify : sys.verify t ap.1 ap.2 <;> simp [hbits, hverify] at hdec
      subst hdec
      exact sys.sound (t := t) (a := ap.1) (pr := ap.2) hverify

/-- Turn an `EncodableProofSystemFamily` into a `CompleteProofCheckerFamily`. -/
noncomputable def toCompleteProofCheckerFamily (sys : EncodableProofSystemFamily (α := α) P) :
    CompleteProofCheckerFamily (α := α) P :=
  { checker := fun t =>
      { decode := sys.decode t
        sound := by
          intro bits a hdec
          exact sys.sound_decode (t := t) hdec
        complete := by
          intro a ha
          rcases sys.complete t a ha with ⟨pr, hpr⟩
          refine ⟨Coding.encodeEncodableBits (α := α × sys.Proof) (a, pr), ?_⟩
          simp [EncodableProofSystemFamily.decode, hpr] } }

end EncodableProofSystemFamily

namespace EncodableSoundProofSystemFamily

variable {α : Type u} [Encodable α] {P : ℕ → α → Prop}

/-- Decode a certificate (bitstring) to a statement `a : α`, accepting it if the bundled proof
object passes `verify`. -/
def decode (sys : EncodableSoundProofSystemFamily (α := α) P) (t : ℕ) : ProofDecoder α :=
  fun bits =>
    match Coding.decodeEncodableBits (α := α × sys.Proof) bits with
    | some ap =>
        let a := ap.1
        let pr := ap.2
        if sys.verify t a pr then some a else none
    | none => none

theorem sound_decode (sys : EncodableSoundProofSystemFamily (α := α) P) {t : ℕ} {bits : List Bool} {a : α}
    (hdec : sys.decode t bits = some a) : P t a := by
  classical
  unfold EncodableSoundProofSystemFamily.decode at hdec
  cases hbits : Coding.decodeEncodableBits (α := α × sys.Proof) bits with
  | none =>
      simp [hbits] at hdec
  | some ap =>
      cases hverify : sys.verify t ap.1 ap.2 <;> simp [hbits, hverify] at hdec
      subst hdec
      exact sys.sound (t := t) (a := ap.1) (pr := ap.2) hverify

/-- Turn an `EncodableSoundProofSystemFamily` into a `ProofCheckerFamily`. -/
def toProofCheckerFamily (sys : EncodableSoundProofSystemFamily (α := α) P) : ProofCheckerFamily (α := α) P :=
  { checker := fun t =>
      { decode := sys.decode t
        sound := by
          intro bits a hdec
          exact sys.sound_decode (t := t) hdec } }

end EncodableSoundProofSystemFamily

end Mettapedia.UniversalAI.TimeBoundedAIXI
