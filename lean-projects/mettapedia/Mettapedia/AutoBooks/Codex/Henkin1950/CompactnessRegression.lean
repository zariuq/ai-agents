import Mettapedia.AutoBooks.Codex.Henkin1950.Compactness

namespace Mettapedia.AutoBooks.Codex.Henkin1950

/-!
# Henkin 1950 Compactness Regression

Positive and negative canaries for the currently trusted compactness-facing
proof-theoretic layer.
-/

namespace Regression

open Mettapedia.Logic.HOL

example
    {T : ClosedTheorySet}
    (hCons : Consistent T) :
    DerivationConsistent T :=
  derivationConsistent_of_consistent hCons

example
    {T : ClosedTheorySet}
    (hFin : FiniteSubsetSatisfiable T) :
    DerivationConsistent T :=
  derivationConsistent_of_finiteSubsetSatisfiable hFin

example
    {T : ClosedTheorySet}
    (hSat : Satisfiable T) :
    DerivationConsistent T :=
  theorem3_forward_derivationConsistent hSat

example
    {T : ClosedTheorySet}
    (hNot : ¬ DerivationConsistent T) :
    ¬ Satisfiable T :=
  not_satisfiable_of_not_derivationConsistent hNot

example
    {T : ClosedTheorySet}
    (hNot : ¬ DerivationConsistent T) :
    ¬ FiniteSubsetSatisfiable T :=
  not_finiteSubsetSatisfiable_of_not_derivationConsistent hNot

example
    {T : ClosedTheorySet}
    (hNot : ¬ DerivationConsistent T) :
    ¬ Consistent T :=
  not_consistent_of_not_derivationConsistent hNot

example
    (hSound : ∀ M : GeneralModel, EqAppArgSound M)
    {T : ClosedTheorySet}
    (hSat : Satisfiable T) :
    Consistent T :=
  theorem3_forward_consistent_of_eqAppArgSound hSound hSat

example
    (hSound : ∀ M : GeneralModel, EqAppArgSound M)
    {T : ClosedTheorySet}
    (hNot : ¬ Consistent T) :
    ¬ Satisfiable T :=
  not_satisfiable_of_inconsistent_of_eqAppArgSound hSound hNot

end Regression

end Mettapedia.AutoBooks.Codex.Henkin1950
