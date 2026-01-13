import Mathlib.Computability.Partrec
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Hutter-style computability notions (Chapter 2, Definition 2.12)

This file provides a small Lean interface for the computability terminology used by
Marcus Hutter, *Universal Artificial Intelligence* (2005), Chapter 2, Definition 2.12.

Mathlib's computability framework (`Computable` / `Partrec`) only applies to outputs with a
`Primcodable` instance, hence it does not directly cover real numbers. To avoid introducing
non-`Primcodable` outputs, we express weaker real-valued notions via **computable dyadic
approximations** (`ℕ`-valued sequences interpreted as `a / 2^n`).

This is enough for Chapter‑2 statements like "`K` is not finitely computable" (Theorem 2.13)
and for later semimeasure enumerability work.
-/

namespace Mettapedia.Computability.Hutter

open scoped Classical

/-- Hutter: "finitely computable" (aka recursive) = total computable function.

This notion is only defined when the output type is `Primcodable`.
-/
def FinitelyComputable {α β : Type*} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Computable f

/-- Interpret a dyadic rational approximation `a / 2^n` as a real number. -/
noncomputable def dyadic (a n : ℕ) : ℝ :=
  (a : ℝ) / (2 : ℝ) ^ n

/-- Hutter: "approximable" real-valued function.

`f` is approximable if there exists a total computable dyadic approximation sequence converging
(to `f x`) without a required convergence rate.
-/
def Approximable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  ∃ a : α → ℕ → ℕ,
    Computable₂ a ∧
      ∀ x : α, Filter.Tendsto (fun n => dyadic (a x n) n) Filter.atTop (nhds (f x))

/-- Hutter: "lower semicomputable" / "enumerable" real-valued function.

We require a computable **monotone increasing** dyadic approximation converging to `f x`.
-/
def LowerSemicomputable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  ∃ a : α → ℕ → ℕ,
    Computable₂ a ∧
      (∀ x : α, Monotone (fun n => dyadic (a x n) n)) ∧
      ∀ x : α, Filter.Tendsto (fun n => dyadic (a x n) n) Filter.atTop (nhds (f x))

/-- Hutter: "upper semicomputable" / "co-enumerable" real-valued function.

We require a computable **monotone decreasing** dyadic approximation converging to `f x`.
-/
def UpperSemicomputable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  ∃ a : α → ℕ → ℕ,
    Computable₂ a ∧
      (∀ x : α, Antitone (fun n => dyadic (a x n) n)) ∧
      ∀ x : α, Filter.Tendsto (fun n => dyadic (a x n) n) Filter.atTop (nhds (f x))

/-- Hutter's terminology: enumerable = lower semicomputable. -/
def Enumerable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  LowerSemicomputable f

/-- Hutter's terminology: co-enumerable = upper semicomputable. -/
def CoEnumerable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  UpperSemicomputable f

/-- Hutter: "estimable" real-valued function.

We use a standard effective approximation definition: there exists a total computable dyadic
approximation with an explicit error bound `2^{-n}`.
-/
def Estimable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  ∃ a : α → ℕ → ℕ,
    Computable₂ a ∧
      ∀ x : α, ∀ n : ℕ, |dyadic (a x n) n - f x| ≤ (1 : ℝ) / (2 : ℝ) ^ n

end Mettapedia.Computability.Hutter
