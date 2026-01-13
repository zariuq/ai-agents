import Mathlib.Data.Nat.Bits
import Mathlib.Logic.Encodable.Basic

/-!
# Chapter 7: Bitstring ↔ ℕ coding utilities (extracted)

These definitions live in the `TimeBoundedAIXI.Coding` namespace because the Chapter 7 development
uses them to decode programs (as `Encodable` objects) from bitstrings.

They are extracted so other modules can use `Coding.decodeEncodableBits` without importing the full
Chapter 7 development file.
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI.Coding

universe u

/-! ## Bitstrings as naturals (little-endian) -/

def bitsToNatLE : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsToNatLE bs

theorem bitsToNatLE_bits (n : ℕ) : bitsToNatLE n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero =>
      simp [bitsToNatLE]
  | bit b n hn ih =>
      -- `Nat.bits` is least-significant-bit first, matching `bitsToNatLE`.
      simp [bitsToNatLE, Nat.bits_append_bit _ _ hn, ih]
      cases b <;> simp [Nat.bit_val, Nat.add_comm]

def decodeNatBits (bits : List Bool) : ℕ :=
  bitsToNatLE bits

def encodeNatBits (n : ℕ) : List Bool :=
  n.bits

@[simp] theorem decodeNatBits_encodeNatBits (n : ℕ) : decodeNatBits (encodeNatBits n) = n := by
  simp [decodeNatBits, encodeNatBits, bitsToNatLE_bits]

def encodeEncodableBits {α : Type u} [Encodable α] (a : α) : List Bool :=
  encodeNatBits (Encodable.encode a)

def decodeEncodableBits {α : Type u} [Encodable α] (bits : List Bool) : Option α :=
  Encodable.decode (decodeNatBits bits)

@[simp] theorem decodeEncodableBits_encodeEncodableBits {α : Type u} [Encodable α] (a : α) :
    decodeEncodableBits (encodeEncodableBits a) = some a := by
  simp [decodeEncodableBits, encodeEncodableBits, decodeNatBits, encodeNatBits, bitsToNatLE_bits,
    Encodable.encodek]

end Mettapedia.UniversalAI.TimeBoundedAIXI.Coding
