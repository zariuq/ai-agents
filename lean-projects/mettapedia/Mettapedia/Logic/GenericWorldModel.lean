import Mettapedia.Logic.PLNWorldModelGeneric

/-!
# Generic World Models

Public front door for additive world models with arbitrary evidence carriers.

This module intentionally drops the PLN-specific framing from the generic layer:

- `PLNWorldModel.WorldModel` remains the binary PLN-facing specialization
- `GenericWorldModel` is the broader additive interface over an arbitrary carrier `Ev`

The current implementation is re-exported from the compatibility module
`PLNWorldModelGeneric`; callers should prefer this module and namespace.
-/

namespace Mettapedia.Logic

export Mettapedia.Logic.PLNWorldModelGeneric
  (GenericWorldModel
   instGenericWorldModelOfWorldModel)

namespace GenericWorldModel

export Mettapedia.Logic.PLNWorldModelGeneric.GenericWorldModel
  (evidence_add'
   GMQueryEq
   queryObservationCount
   queryObservationConfidence
   evidence_eq_binary_evidence
   queryObservationCount_eq_binary_total
   queryObservationConfidence_eq_queryConfidence
   genericWorldModelOfAtomicEvidence
   queryObservationCount_of_unit
   queryObservationConfidence_of_unit
   queryObservationCount_eq_zero_of_revision_idempotent
   not_revision_idempotent_of_finite_nonzero_queryObservationCount
   dirichlet_queryObservationCount_of_single)

namespace GMQueryEq

export Mettapedia.Logic.PLNWorldModelGeneric.GenericWorldModel.GMQueryEq
  (refl
   symm
   trans
   to_queryObservationCount
   to_queryObservationConfidence)

end GMQueryEq
end GenericWorldModel
end Mettapedia.Logic
