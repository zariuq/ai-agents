import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.Basic
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.FiniteHorizon
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.CompetitorBounds
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.HutterEnumeration
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.HutterEnumerationTheoremSemimeasure
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.SolomonoffBridge

/-!
# Universal Prediction (Finite Alphabet) — Master Import

This module provides a single import point for the finite-alphabet universal prediction stack:

* core semimeasures/prefix measures on `Word α := List α`
* finite-horizon relative entropy / dominance→regret bounds
* Hutter-style lower-semicomputable semimeasure enumeration (concrete via `Nat.Partrec.Code`)
* the resulting theorem-grade “Solomonoff-style” universal mixture `M₂`

The corresponding binary-specialized development remains in:
* `Mettapedia.Logic.UniversalPrediction` and `.../SolomonoffBridge.lean`.
-/
