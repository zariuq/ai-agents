import Mettapedia.OSLF.Framework.PyashCoreModel

namespace Mettapedia.OSLF.Framework.PyashCoreInstance

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Positive native-type witness: a canonical Pyash state shape is accepted by `pyashStateTop`. -/
def pyashStateTopPositiveExample : Pattern :=
  .apply "State"
    [ .apply "DeriveSignature" []
    , .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], .apply "RTNil" []]
    , .apply "Signature" [.apply "VRead" [], .apply "RTNil" []]
    , .apply "Ok" []
    ]

/-- Negative native-type witness: non-`State` constructor is rejected by `pyashStateTop`. -/
def pyashStateTopNegativeNonStateExample : Pattern :=
  .apply "DeriveSignature" []

/-- Negative native-type witness: malformed outcome constructor is rejected by `pyashStateTop`. -/
def pyashStateTopNegativeBadOutcomeExample : Pattern :=
  .apply "State"
    [ .apply "DeriveSignature" []
    , .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], .apply "RTNil" []]
    , .apply "Signature" [.apply "VRead" [], .apply "RTNil" []]
    , .apply "VRead" []
    ]

theorem pyashStateTop_accepts_positive_example :
    pyashStateTop.pred pyashStateTopPositiveExample := by
  unfold pyashStateTop pyashStateTopPositiveExample
  simp [isPyashState, isPyashInstr, isPyashSentence, isPyashMood, isPyashVerb,
    isPyashRoleTypes, isPyashSignature, isPyashOutcome]

theorem pyashStateTop_rejects_non_state_example :
    ¬ pyashStateTop.pred pyashStateTopNegativeNonStateExample := by
  unfold pyashStateTop pyashStateTopNegativeNonStateExample
  simp [isPyashState]

theorem pyashStateTop_rejects_bad_outcome_example :
    ¬ pyashStateTop.pred pyashStateTopNegativeBadOutcomeExample := by
  unfold pyashStateTop pyashStateTopNegativeBadOutcomeExample
  simp [isPyashState, isPyashInstr, isPyashSentence, isPyashMood, isPyashVerb,
    isPyashRoleTypes, isPyashSignature, isPyashOutcome]

end Mettapedia.OSLF.Framework.PyashCoreInstance
