import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Active Minimal Surface)

This module intentionally keeps only a minimal active entrypoint while the
previous large development remains archived.
-/

namespace Mettapedia.Logic
namespace MarkovDeFinetti

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

variable {k : ℕ}

/-- Minimal predicate used by active Fortini/anchor plumbing. -/
def IsMarkovExchangeablePrefixMeasure
    (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  MarkovExchangeablePrefixMeasure (k := k) μ

end MarkovDeFinetti
end Mettapedia.Logic
