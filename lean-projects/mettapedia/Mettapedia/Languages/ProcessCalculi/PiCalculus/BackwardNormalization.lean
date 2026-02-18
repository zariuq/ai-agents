import Mettapedia.Languages.ProcessCalculi.PiCalculus.RhoEncoding
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context

/-!
# Backward Normalization Helpers for π→ρ

Small normalization lemmas for backward/reflection proofs:
- explicit flattened bag shape for key admin sources
- canonical COMM-shape permutations
- SC bridges from encoded sources to COMM-ready shapes
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

/-- Positive normalization example: a bag is already in component form. -/
theorem parComponents_bag_example (elems : List Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
      (.collection .hashBag elems none) = elems := by
  rfl

/-- Negative normalization example: a non-bag stays as a singleton component list. -/
theorem parComponents_nonbag_example (p : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context.parComponents
      (.apply "PDrop" [p]) = [.apply "PDrop" [p]] := by
  rfl

/-- Canonical COMM redex bag shape from normalized components. -/
def commRedexShape (n q p : Pattern) (rest : List Pattern) : Pattern :=
  .collection .hashBag (rhoOutput n q :: .apply "PInput" [n, .lambda p] :: rest) none

/-- Canonical COMM target bag shape from normalized components. -/
def commTargetShape (q p : Pattern) (rest : List Pattern) : Pattern :=
  .collection .hashBag (Mettapedia.OSLF.MeTTaIL.Substitution.commSubst p q :: rest) none

/-- Reusable SC normalization bridge:
any source that normalizes to a bag permutation of a COMM redex
is SC-equivalent to that COMM redex shape. -/
theorem source_sc_commRedex_of_eq_bag_perm
    {src : Pattern} {elems rest : List Pattern} {n q p : Pattern}
    (hsrc : src = .collection .hashBag elems none)
    (hperm : elems.Perm (rhoOutput n q :: .apply "PInput" [n, .lambda p] :: rest)) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      src (commRedexShape n q p rest) := by
  calc
    src = .collection .hashBag elems none := hsrc
    _ ≡ commRedexShape n q p rest := by
          simpa [commRedexShape] using
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_perm
              elems (rhoOutput n q :: .apply "PInput" [n, .lambda p] :: rest) hperm)

/-- Candidate COMM reduction from the canonical normalized redex shape. -/
def commRedexShape_reduces (n q p : Pattern) (rest : List Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (commRedexShape n q p rest)
      (commTargetShape q p rest) := by
  simpa [commRedexShape, commTargetShape] using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.comm
      (n := n) (q := q) (p := p) (rest := rest))

/-- Reusable COMM decomposition endpoint from normalized bags:
SC normalization into COMM redex + candidate COMM step. -/
theorem comm_decompose_from_normalized_bag
    {src : Pattern} {elems rest : List Pattern} {n q p : Pattern}
    (hsrc : src = .collection .hashBag elems none)
    (hperm : elems.Perm (rhoOutput n q :: .apply "PInput" [n, .lambda p] :: rest)) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      src (commRedexShape n q p rest) ∧
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (commRedexShape n q p rest)
      (commTargetShape q p rest)) := by
  exact ⟨source_sc_commRedex_of_eq_bag_perm hsrc hperm, ⟨commRedexShape_reduces n q p rest⟩⟩

/-- Specialized COMM decomposition for encoded-image bags:
an encoded top-level input and output on the same channel form a COMM candidate
after a single head permutation. -/
theorem comm_decompose_encoded_source
    (x y z : Name) (P : Process) (n v : String) (rest : List Pattern) :
    let inp : Pattern := rhoInput (.fvar x) y (encode P n v)
    let out : Pattern := rhoOutput (.fvar x) (rhoDrop (.fvar z))
    let src : Pattern := .collection .hashBag (inp :: out :: rest) none
    let redex : Pattern :=
      commRedexShape (.fvar x) (.apply "PDrop" [.fvar z])
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P n v)) rest
    let tgt : Pattern :=
      commTargetShape (.apply "PDrop" [.fvar z])
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P n v)) rest
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src redex ∧
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces redex tgt) := by
  intro inp out src redex tgt
  have hperm :
      (inp :: out :: rest).Perm
        (rhoOutput (.fvar x) (.apply "PDrop" [.fvar z]) ::
          .apply "PInput" [.fvar x,
            .lambda
              (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P n v))] :: rest) := by
    simpa [inp, out, rhoInput, rhoOutput, rhoDrop] using
      (List.Perm.swap inp out rest).symm
  simpa [src, redex, tgt] using
    (comm_decompose_from_normalized_bag
      (src := src)
      (elems := inp :: out :: rest)
      (rest := rest)
      (n := .fvar x)
      (q := .apply "PDrop" [.fvar z])
      (p := Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 y (encode P n v))
      rfl hperm)

/-- Canonical ν-listener source bag used for COMM decomposition. -/
def nuListenerSource (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) : Pattern :=
  rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda listenerBody])

/-- Canonical ν-listener COMM-redex shape. -/
def nuListenerPreComm (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [rhoOutput (.fvar v) (.fvar n),
     .apply "PInput" [.fvar v, .lambda listenerBody],
     rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none

/-- Canonical ν-listener COMM target. -/
def nuListenerTarget (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
     rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none

/-- Flattened source shape for the ν-listener administrative step. -/
theorem nu_listener_source_eq_bag
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    nuListenerSource x P n v listenerBody =
      .collection .hashBag
        [rhoOutput (.fvar v) (.fvar n),
         rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v),
         .apply "PInput" [.fvar v, .lambda listenerBody]] none := by
  simp [nuListenerSource, encode, rhoPar, rhoInput, rhoOutput]

/-- Permutation from flattened ν source to COMM-ready shape. -/
theorem nu_listener_comm_shape_perm
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    ([rhoOutput (.fvar v) (.fvar n),
      rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v),
      .apply "PInput" [.fvar v, .lambda listenerBody]] : List Pattern).Perm
    [rhoOutput (.fvar v) (.fvar n),
     .apply "PInput" [.fvar v, .lambda listenerBody],
     rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] := by
  refine List.Perm.cons _ ?_
  simpa using (List.Perm.swap
    (rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v))
    (.apply "PInput" [.fvar v, .lambda listenerBody])
    ([] : List Pattern)).symm

/-- SC bridge: ν-listener source into COMM-ready shape. -/
theorem nu_listener_source_sc_comm_shape
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nuListenerSource x P n v listenerBody)
      (nuListenerPreComm x P n v listenerBody) := by
  calc
    nuListenerSource x P n v listenerBody =
        .collection .hashBag
          [rhoOutput (.fvar v) (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v),
           .apply "PInput" [.fvar v, .lambda listenerBody]] none := by
            simpa using nu_listener_source_eq_bag x P n v listenerBody
    _ ≡ nuListenerPreComm x P n v listenerBody := by
            exact
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_perm _ _
                (nu_listener_comm_shape_perm x P n v listenerBody)

/-- Candidate COMM reduction on the canonical ν-listener COMM-redex shape. -/
def nu_listener_preComm_reduces
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nuListenerPreComm x P n v listenerBody)
      (nuListenerTarget x P n v listenerBody) := by
  simpa [nuListenerPreComm, nuListenerTarget] using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.comm
      (n := (.fvar v))
      (q := (.fvar n))
      (p := listenerBody)
      (rest := [rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)]))

/-- COMM decomposition endpoint for ν-listener sources:
SC normalization + candidate COMM step to canonical target. -/
theorem nu_listener_comm_decompose
    (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nuListenerSource x P n v listenerBody)
      (nuListenerPreComm x P n v listenerBody) ∧
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nuListenerPreComm x P n v listenerBody)
      (nuListenerTarget x P n v listenerBody)) := by
  exact ⟨nu_listener_source_sc_comm_shape x P n v listenerBody,
    ⟨nu_listener_preComm_reduces x P n v listenerBody⟩⟩

/-- Canonical name-server listener source bag used for COMM decomposition. -/
def nameServerListenerSource (x z v s : String) (listenerBody : Pattern) : Pattern :=
  rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda listenerBody])

/-- Canonical name-server listener COMM-redex shape. -/
def nameServerListenerPreComm (x z v s : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
     .apply "PInput" [.fvar z, .lambda listenerBody],
     rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
     dropOperation x] none

/-- Canonical name-server listener COMM target. -/
def nameServerListenerTarget (x z v s : String) (listenerBody : Pattern) : Pattern :=
  .collection .hashBag
    [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.apply "PDrop" [.fvar s]),
     rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
     dropOperation x] none

/-- Flattened source shape for the name-server listener administrative step. -/
theorem nameServer_listener_source_eq_bag
    (x z v s : String) (listenerBody : Pattern) :
    nameServerListenerSource x z v s listenerBody =
      .collection .hashBag
        [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
         dropOperation x,
         rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
         .apply "PInput" [.fvar z, .lambda listenerBody]] none := by
  simp [nameServerListenerSource, nameServer, rhoPar, rhoReplicate, dropOperation, rhoOutput]

/-- Permutation from flattened seed-listener source to COMM-ready shape. -/
theorem nameServer_listener_comm_shape_perm
    (x z v s : String) (listenerBody : Pattern) :
    ([rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
      dropOperation x,
      rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
      .apply "PInput" [.fvar z, .lambda listenerBody]] : List Pattern).Perm
    [rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
     .apply "PInput" [.fvar z, .lambda listenerBody],
     rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
     dropOperation x] := by
  simpa using
    (show (([rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v), dropOperation x] ++
        [rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]), .apply "PInput" [.fvar z, .lambda listenerBody]]) : List Pattern).Perm
        (([rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]), .apply "PInput" [.fvar z, .lambda listenerBody]] ++
          [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v), dropOperation x]) : List Pattern) from
      List.perm_append_comm)

/-- SC bridge: name-server listener source into COMM-ready shape. -/
theorem nameServer_listener_source_sc_comm_shape
    (x z v s : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nameServerListenerSource x z v s listenerBody)
      (nameServerListenerPreComm x z v s listenerBody) := by
  calc
    nameServerListenerSource x z v s listenerBody =
        .collection .hashBag
          [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x,
           rhoOutput (.fvar z) (.apply "PDrop" [.fvar s]),
           .apply "PInput" [.fvar z, .lambda listenerBody]] none := by
            simpa using nameServer_listener_source_eq_bag x z v s listenerBody
    _ ≡ nameServerListenerPreComm x z v s listenerBody := by
            exact
              Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_perm _ _
                (nameServer_listener_comm_shape_perm x z v s listenerBody)

/-- Candidate COMM reduction on the canonical name-server listener COMM-redex shape. -/
def nameServer_listener_preComm_reduces
    (x z v s : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nameServerListenerPreComm x z v s listenerBody)
      (nameServerListenerTarget x z v s listenerBody) := by
  simpa [nameServerListenerPreComm, nameServerListenerTarget] using
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.comm
      (n := (.fvar z))
      (q := (.apply "PDrop" [.fvar s]))
      (p := listenerBody)
      (rest := [rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v), dropOperation x]))

/-- COMM decomposition endpoint for name-server listener sources:
SC normalization + candidate COMM step to canonical target. -/
theorem nameServer_listener_comm_decompose
    (x z v s : String) (listenerBody : Pattern) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (nameServerListenerSource x z v s listenerBody)
      (nameServerListenerPreComm x z v s listenerBody) ∧
    Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces
      (nameServerListenerPreComm x z v s listenerBody)
      (nameServerListenerTarget x z v s listenerBody)) := by
  exact ⟨nameServer_listener_source_sc_comm_shape x z v s listenerBody,
    ⟨nameServer_listener_preComm_reduces x z v s listenerBody⟩⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization
