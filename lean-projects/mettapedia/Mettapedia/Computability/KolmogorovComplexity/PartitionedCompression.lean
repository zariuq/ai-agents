import Mettapedia.Computability.KolmogorovComplexity.Basic

/-!
# Partitioned Compression Obstruction

This file isolates a general counting obstruction for case-split compression.

Suppose all binary strings of length `n` are partitioned into finitely many
fibers, and each fiber admits an injective encoder into bitstrings whose length
is bounded by some budget depending on the fiber. Then the whole class size is
bounded by the sum of those code capacities.

This is a Tim-free public theorem: it does not mention any particular dynamics,
only finite partitions and code budgets. Private projects can later instantiate
it with manuscript-specific predicates or slice decompositions.
-/

namespace KolmogorovComplexity

open scoped Classical

/-- Binary strings of exact length `n`. -/
abbrev StringsOfLength (n : ℕ) := List.Vector Bool n

/-- Binary codes of length at most `c`, represented by a length tag together with
the payload at that length. -/
abbrev CodesUpTo (c : ℕ) := Σ l : Fin (c + 1), List.Vector Bool l.1

/-- There are exactly `2^n` binary strings of length `n`. -/
theorem card_stringsOfLength (n : ℕ) : Fintype.card (StringsOfLength n) = 2 ^ n := by
  simp [StringsOfLength, card_vector]

/-- The bounded code space `CodesUpTo c` has cardinality `2^(c+1) - 1`. -/
theorem card_codesUpTo (c : ℕ) : Fintype.card (CodesUpTo c) = 2 ^ (c + 1) - 1 := by
  have hcard : Fintype.card (CodesUpTo c) = ∑ l : Fin (c + 1), (2 : ℕ) ^ (l : ℕ) := by
    simp [CodesUpTo, Fintype.card_sigma, card_vector]
  have hgeomRange : (∑ t ∈ Finset.range (c + 1), (2 : ℕ) ^ t) = 2 ^ (c + 1) - 1 := by
    calc
      ∑ t ∈ Finset.range (c + 1), (2 : ℕ) ^ t = ((2 : ℕ) ^ (c + 1) - 1) / (2 - 1) := by
        simpa using (Nat.geomSum_eq (m := 2) (n := c + 1) (by decide : 2 ≤ (2 : ℕ)))
      _ = 2 ^ (c + 1) - 1 := by simp
  calc
    Fintype.card (CodesUpTo c) = ∑ l : Fin (c + 1), (2 : ℕ) ^ (l : ℕ) := hcard
    _ = ∑ t ∈ Finset.range (c + 1), (2 : ℕ) ^ t := by
      simp [Fin.sum_univ_eq_sum_range]
    _ = 2 ^ (c + 1) - 1 := hgeomRange

/-- Repackage a partition function on any finite type as a sigma of its fibers. -/
def partitionFiberEquivOfFinite {X : Type} [Fintype X] {ι : Type} (branch : X → ι) :
    X ≃ Σ i : ι, {x : X // branch x = i} where
  toFun x := ⟨branch x, ⟨x, rfl⟩⟩
  invFun y := y.2.1
  left_inv x := rfl
  right_inv y := by
    cases y with
    | mk i x =>
        cases x with
        | mk x hx =>
            cases hx
            rfl

/-- The fibers of a partition function on a finite type have total cardinality equal
to the domain cardinality. -/
theorem card_partitionFibersOfFinite {X : Type} [Fintype X] {ι : Type} [Fintype ι]
    (branch : X → ι) :
    Fintype.card X = ∑ i : ι, Fintype.card {x : X // branch x = i} := by
  calc
    Fintype.card X = Fintype.card (Σ i : ι, {x : X // branch x = i}) := by
      exact Fintype.card_congr (partitionFiberEquivOfFinite branch)
    _ = ∑ i : ι, Fintype.card {x : X // branch x = i} := by
      simp [Fintype.card_sigma]

/-- If each partition fiber of a finite type injects into a bounded code space, then the total
class size is bounded by the sum of the fiber code capacities. -/
theorem card_partitionedEncoding_le_of_finite
    {X : Type} [Fintype X] {ι : Type} [Fintype ι]
    (branch : X → ι)
    (budget : ι → ℕ)
    (encode : ∀ i : ι, {x : X // branch x = i} → CodesUpTo (budget i))
    (hinj : ∀ i : ι, Function.Injective (encode i)) :
    Fintype.card X ≤ ∑ i : ι, (2 ^ (budget i + 1) - 1) := by
  calc
    Fintype.card X = ∑ i : ι, Fintype.card {x : X // branch x = i} :=
      card_partitionFibersOfFinite branch
    _ ≤ ∑ i : ι, Fintype.card (CodesUpTo (budget i)) := by
      exact Finset.sum_le_sum (fun i _ => Fintype.card_le_of_injective (encode i) (hinj i))
    _ = ∑ i : ι, (2 ^ (budget i + 1) - 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact card_codesUpTo (budget i)

/-- If the total code budget is smaller than the domain size, then no such
partitioned family of injective encoders can exist. -/
theorem no_partitionedEncoding_of_lt_sumBudgets_of_finite
    {X : Type} [Fintype X] {ι : Type} [Fintype ι]
    (branch : X → ι)
    (budget : ι → ℕ)
    (hsmall : (∑ i : ι, (2 ^ (budget i + 1) - 1)) < Fintype.card X) :
    ¬ ∃ encode : ∀ i : ι, {x : X // branch x = i} → CodesUpTo (budget i),
        ∀ i : ι, Function.Injective (encode i) := by
  rintro ⟨encode, hinj⟩
  have hbound := card_partitionedEncoding_le_of_finite branch budget encode hinj
  exact Nat.not_le_of_lt hsmall hbound

/-- Two-branch specialization on an arbitrary finite domain. -/
theorem card_twoWayEncoding_le_of_finite
    {X : Type} [Fintype X]
    (branch : X → Bool)
    (budgetTrue budgetFalse : ℕ)
    (encodeTrue : {x : X // branch x = true} → CodesUpTo budgetTrue)
    (encodeFalse : {x : X // branch x = false} → CodesUpTo budgetFalse)
    (hinjTrue : Function.Injective encodeTrue)
    (hinjFalse : Function.Injective encodeFalse) :
    Fintype.card X ≤ (2 ^ (budgetTrue + 1) - 1) + (2 ^ (budgetFalse + 1) - 1) := by
  simpa using
    (card_partitionedEncoding_le_of_finite
      (branch := branch)
      (budget := fun b : Bool => cond b budgetTrue budgetFalse)
      (encode := fun b =>
        match b with
        | true => encodeTrue
        | false => encodeFalse)
      (hinj := by
        intro b
        cases b with
        | false => simpa using hinjFalse
        | true => simpa using hinjTrue))

/-- Repackage a partition function as a sigma of its fibers. -/
def partitionFiberEquiv {n : ℕ} {ι : Type} (branch : StringsOfLength n → ι) :
    StringsOfLength n ≃ Σ i : ι, {x : StringsOfLength n // branch x = i} :=
  partitionFiberEquivOfFinite branch

/-- The fibers of a partition function have total cardinality `2^n`. -/
theorem card_partitionFibers {n : ℕ} {ι : Type} [Fintype ι]
    (branch : StringsOfLength n → ι) :
    2 ^ n = ∑ i : ι, Fintype.card {x : StringsOfLength n // branch x = i} := by
  calc
    2 ^ n = Fintype.card (StringsOfLength n) := by symm; exact card_stringsOfLength n
    _ = ∑ i : ι, Fintype.card {x : StringsOfLength n // branch x = i} := by
      exact card_partitionFibersOfFinite branch

/-- If each partition fiber injects into a bounded code space, then the total
class size is bounded by the sum of the fiber code capacities. -/
theorem card_partitionedEncoding_le {n : ℕ} {ι : Type} [Fintype ι]
    (branch : StringsOfLength n → ι)
    (budget : ι → ℕ)
    (encode : ∀ i : ι, {x : StringsOfLength n // branch x = i} → CodesUpTo (budget i))
    (hinj : ∀ i : ι, Function.Injective (encode i)) :
    2 ^ n ≤ ∑ i : ι, (2 ^ (budget i + 1) - 1) := by
  calc
    2 ^ n = Fintype.card (StringsOfLength n) := by symm; exact card_stringsOfLength n
    _ ≤ ∑ i : ι, (2 ^ (budget i + 1) - 1) := by
      exact card_partitionedEncoding_le_of_finite branch budget encode hinj

/-- If the total code budget is smaller than the full class size `2^n`, then no
such partitioned family of injective encoders can exist. -/
theorem no_partitionedEncoding_of_lt_sumBudgets {n : ℕ} {ι : Type} [Fintype ι]
    (branch : StringsOfLength n → ι)
    (budget : ι → ℕ)
    (hsmall : (∑ i : ι, (2 ^ (budget i + 1) - 1)) < 2 ^ n) :
    ¬ ∃ encode : ∀ i : ι, {x : StringsOfLength n // branch x = i} → CodesUpTo (budget i),
        ∀ i : ι, Function.Injective (encode i) := by
  exact no_partitionedEncoding_of_lt_sumBudgets_of_finite branch budget
    (by simpa [card_stringsOfLength n] using hsmall)

/-- Two-branch specialization, convenient for front/nonfront or any other
binary case split. -/
theorem card_twoWayEncoding_le {n : ℕ}
    (branch : StringsOfLength n → Bool)
    (budgetTrue budgetFalse : ℕ)
    (encodeTrue : {x : StringsOfLength n // branch x = true} → CodesUpTo budgetTrue)
    (encodeFalse : {x : StringsOfLength n // branch x = false} → CodesUpTo budgetFalse)
    (hinjTrue : Function.Injective encodeTrue)
    (hinjFalse : Function.Injective encodeFalse) :
    2 ^ n ≤ (2 ^ (budgetTrue + 1) - 1) + (2 ^ (budgetFalse + 1) - 1) := by
  calc
    2 ^ n = Fintype.card (StringsOfLength n) := by symm; exact card_stringsOfLength n
    _ ≤ (2 ^ (budgetTrue + 1) - 1) + (2 ^ (budgetFalse + 1) - 1) := by
      exact card_twoWayEncoding_le_of_finite branch budgetTrue budgetFalse
        encodeTrue encodeFalse hinjTrue hinjFalse

end KolmogorovComplexity
