import Mathlib.Computability.PostTuringMachine

open Relation

namespace Scratch

universe u

def runFor {σ : Type u} (step : σ → Option σ) : ℕ → σ → σ
  | 0, s => s
  | n + 1, s =>
      match step s with
      | none => s
      | some s' => runFor step n s'

def reachesLength {σ : Type u} {step : σ → Option σ} {a b : σ} :
    Turing.Reaches step a b → ℕ
  | .refl => 0
  | .tail h _ => reachesLength h + 1

example {σ : Type u} {step : σ → Option σ} {a b : σ} (h : Turing.Reaches step a b) : True := by
  induction h with
  | refl =>
      trivial
  | tail hab hstep ih =>
      -- show variables?
      trivial

end Scratch
