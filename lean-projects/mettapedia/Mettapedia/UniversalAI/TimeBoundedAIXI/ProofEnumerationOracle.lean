import Mettapedia.UniversalAI.TimeBoundedAIXI.ProofEnumeration
import Mettapedia.UniversalAI.TimeBoundedAIXI.CodingBits

/-!
# Chapter 7: A concrete (oracle-style) complete proof checker

Chapter 7 models “provability of `VA(p)`” via an abstract `CompleteProofChecker`.  This file
provides a *concrete* instantiation for any **encodable** object-language:

- Certificates are bitstrings encoding an `α` value via `Coding.decodeEncodableBits`.
- The checker accepts exactly those decoded values satisfying the target predicate `P`.

This is *not* intended as a faithful computability model of a real proof system (it bakes `P` into
the checker), but it is a useful baseline instantiation for exercising the Chapter 7 convergence
pipeline without leaving `CompleteProofChecker` abstract.
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI

open scoped Classical

universe u

namespace ProofEnumerationOracle

/-- Decode a certificate (bitstring) to an `α`, and accept it iff `P` holds. -/
noncomputable def oracleDecode {α : Type u} [Encodable α] (P : α → Prop) : ProofDecoder α :=
  fun bits =>
    match Coding.decodeEncodableBits (α := α) bits with
    | some a => if _ : P a then some a else none
    | none => none

/-- A complete proof checker obtained by using `oracleDecode`. -/
noncomputable def oracleCompleteProofChecker {α : Type u} [Encodable α] (P : α → Prop) :
    CompleteProofChecker (α := α) P :=
  { decode := oracleDecode (α := α) P
    sound := by
      intro bits a hdec
      cases h : Coding.decodeEncodableBits (α := α) bits with
      | none =>
          -- contradiction: `none = some a`
          simp [oracleDecode, h] at hdec
      | some a0 =>
          by_cases ha0 : P a0
          · have : a0 = a := by simpa [oracleDecode, h, ha0] using hdec
            subst this
            exact ha0
          · simp [oracleDecode, h, ha0] at hdec
    complete := by
      intro a ha
      refine ⟨Coding.encodeEncodableBits (α := α) a, ?_⟩
      simp [oracleDecode, ha] }

/-- A family of complete proof checkers obtained by using `oracleCompleteProofChecker` pointwise. -/
noncomputable def oracleCompleteProofCheckerFamily {α : Type u} [Encodable α] (P : ℕ → α → Prop) :
    CompleteProofCheckerFamily (α := α) P :=
  { checker := fun t => oracleCompleteProofChecker (α := α) (P t) }

end ProofEnumerationOracle

end Mettapedia.UniversalAI.TimeBoundedAIXI
