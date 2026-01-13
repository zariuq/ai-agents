import Mathlib.Data.List.Basic

/-!
# Chapter 7: Proof enumeration utilities

This module factors out the shared “enumerate bitstrings up to a length bound, decode certificates”
machinery used in the Chapter 7 developments:

- `Mettapedia.UniversalAI.TimeBoundedAIXI` (toy/specialized)
- `Mettapedia.UniversalAI.TimeBoundedAIXI.Core` (core-generic schema)
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI

universe u

/-! ## Enumerating bitstrings up to a length bound -/

/-- Enumerate all bitstrings of a fixed length. -/
def bitstringsOfLength : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitstringsOfLength n).flatMap fun xs => [false :: xs, true :: xs]

/-- Enumerate all bitstrings of length ≤ `n`. -/
def bitstringsUpTo : ℕ → List (List Bool)
  | 0 => bitstringsOfLength 0
  | n + 1 => bitstringsUpTo n ++ bitstringsOfLength (n + 1)

theorem mem_bitstringsOfLength_self (bits : List Bool) : bits ∈ bitstringsOfLength bits.length := by
  induction bits with
  | nil =>
      simp [bitstringsOfLength]
  | cons b bs ih =>
      cases b <;>
        · refine List.mem_flatMap.2 ?_
          refine ⟨bs, ih, ?_⟩
          simp

theorem length_eq_of_mem_bitstringsOfLength {n : ℕ} {bits : List Bool} (h : bits ∈ bitstringsOfLength n) :
    bits.length = n := by
  induction n generalizing bits with
  | zero =>
      simp [bitstringsOfLength] at h
      simp [h]
  | succ n ih =>
      simp [bitstringsOfLength, List.mem_flatMap] at h
      rcases h with ⟨bs, hbs, hb⟩
      have hlen : bs.length = n := ih hbs
      rcases hb with rfl | rfl <;> simp [hlen]

theorem mem_bitstringsUpTo_of_mem_bitstringsOfLength {n : ℕ} {bits : List Bool}
    (h : bits ∈ bitstringsOfLength n) : bits ∈ bitstringsUpTo n := by
  cases n with
  | zero =>
      simpa [bitstringsUpTo] using h
  | succ n =>
      exact List.mem_append_right _ h

theorem mem_bitstringsUpTo_mono {m n : ℕ} (hmn : m ≤ n) {bits : List Bool} (h : bits ∈ bitstringsUpTo m) :
    bits ∈ bitstringsUpTo n := by
  induction hmn with
  | refl =>
      simpa using h
  | @step n hmn ih =>
      exact List.mem_append_left _ ih

theorem mem_bitstringsUpTo_of_length_le {n : ℕ} {bits : List Bool} (h : bits.length ≤ n) :
    bits ∈ bitstringsUpTo n := by
  have h0 : bits ∈ bitstringsUpTo bits.length :=
    mem_bitstringsUpTo_of_mem_bitstringsOfLength (n := bits.length) (mem_bitstringsOfLength_self bits)
  exact mem_bitstringsUpTo_mono (m := bits.length) (n := n) h h0

theorem length_le_of_mem_bitstringsUpTo {n : ℕ} {bits : List Bool} (h : bits ∈ bitstringsUpTo n) :
    bits.length ≤ n := by
  induction n generalizing bits with
  | zero =>
      simp [bitstringsUpTo, bitstringsOfLength] at h
      simp [h]
  | succ n ih =>
      simp [bitstringsUpTo] at h
      rcases h with h | h
      · exact Nat.le_trans (ih h) (Nat.le_succ n)
      · have : bits.length = n + 1 := length_eq_of_mem_bitstringsOfLength (n := n + 1) h
        simp [this]

/-! ## Proof checkers -/

/-- A certificate decoder for proofs encoded as bitstrings. -/
abbrev ProofDecoder (α : Type u) : Type u :=
  List Bool → Option α

/-- Step 1: enumerate proofs up to `l_p` and decode those yielding an `α`. -/
def findValidPrograms {α : Type u} (decode : ProofDecoder α) (l_p : ℕ) : List α :=
  (bitstringsUpTo l_p).filterMap decode

/-- A sound proof checker for the predicate `P`: every decoded certificate satisfies `P`. -/
structure ProofChecker {α : Type u} (P : α → Prop) where
  decode : ProofDecoder α
  sound : ∀ {bits a}, decode bits = some a → P a

namespace ProofChecker

variable {α : Type u} {P : α → Prop}

theorem mem_findValidPrograms_iff_exists_bits (decode : ProofDecoder α) (l_p : ℕ) (a : α) :
    a ∈ findValidPrograms decode l_p ↔ ∃ bits ∈ bitstringsUpTo l_p, decode bits = some a := by
  simp [findValidPrograms, List.mem_filterMap]

theorem mem_findValidPrograms_of_decode_of_length_le {decode : ProofDecoder α} {l_p : ℕ}
    {bits : List Bool} {a : α} (hbits : bits.length ≤ l_p) (hdec : decode bits = some a) :
    a ∈ findValidPrograms decode l_p := by
  unfold findValidPrograms
  refine (List.mem_filterMap).2 ?_
  refine ⟨bits, mem_bitstringsUpTo_of_length_le hbits, hdec⟩

theorem exists_bits_of_mem_findValidPrograms {decode : ProofDecoder α} {l_p : ℕ} {a : α}
    (ha : a ∈ findValidPrograms decode l_p) :
    ∃ bits, bits.length ≤ l_p ∧ decode bits = some a := by
  unfold findValidPrograms at ha
  rcases (List.mem_filterMap).1 ha with ⟨bits, hbits, hdec⟩
  exact ⟨bits, length_le_of_mem_bitstringsUpTo hbits, hdec⟩

theorem sound_of_mem_findValidPrograms (checker : ProofChecker (α := α) P) {l_p : ℕ} {a : α}
    (ha : a ∈ findValidPrograms checker.decode l_p) : P a := by
  rcases exists_bits_of_mem_findValidPrograms (decode := checker.decode) (l_p := l_p) (a := a) ha with
    ⟨bits, _hbits, hdec⟩
  exact checker.sound hdec

end ProofChecker

/-- A sound proof checker that is also complete for `P`: every `a` satisfying `P` has a certificate. -/
structure CompleteProofChecker {α : Type u} (P : α → Prop) extends ProofChecker (α := α) P where
  complete : ∀ a, P a → ∃ bits, decode bits = some a

namespace CompleteProofChecker

variable {α : Type u} {P : α → Prop}

theorem exists_mem_findValidPrograms (checker : CompleteProofChecker (α := α) P) {a : α} (ha : P a) :
    ∃ l_p, a ∈ findValidPrograms checker.decode l_p := by
  rcases checker.complete a ha with ⟨bits, hdec⟩
  refine ⟨bits.length, ?_⟩
  exact
    ProofChecker.mem_findValidPrograms_of_decode_of_length_le (decode := checker.decode) (l_p := bits.length)
      (hbits := Nat.le_refl bits.length) (hdec := hdec)

theorem exists_bound_forall_mem_findValidPrograms (checker : CompleteProofChecker (α := α) P) {a : α} (ha : P a) :
    ∃ N, ∀ l_p ≥ N, a ∈ findValidPrograms checker.decode l_p := by
  rcases checker.complete a ha with ⟨bits, hdec⟩
  refine ⟨bits.length, ?_⟩
  intro l_p hlp
  exact
    ProofChecker.mem_findValidPrograms_of_decode_of_length_le (decode := checker.decode) (l_p := l_p)
      (hbits := hlp) (hdec := hdec)

end CompleteProofChecker

/-- A family of complete proof checkers indexed by a parameter (typically the per-cycle time bound `t`). -/
structure CompleteProofCheckerFamily {α : Type u} (P : ℕ → α → Prop) where
  checker : ∀ t : ℕ, CompleteProofChecker (α := α) (P t)

/-- A family of sound proof checkers indexed by a parameter (typically the per-cycle time bound `t`). -/
structure ProofCheckerFamily {α : Type u} (P : ℕ → α → Prop) where
  checker : ∀ t : ℕ, ProofChecker (α := α) (P t)

end Mettapedia.UniversalAI.TimeBoundedAIXI
