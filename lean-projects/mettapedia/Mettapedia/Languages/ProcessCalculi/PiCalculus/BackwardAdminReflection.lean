import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization

/-!
# Backward Admin Reflection (π→ρ, Derived Layer)

This module starts the backward side by packaging reflected structure from the
proved non-RF administrative forward closure:

- encoded-image closure up to structural congruence (`EncodedSC`)
- reflected witnesses for combined ν/seed/replicate administrative traces
- concrete and nontrivial canaries
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism

/-- Encoded image closed under ρ structural congruence. -/
def EncodedSC (n v : String) (p : Pattern) : Prop :=
  ∃ p0, EncodingMorphism.Encoded n v p0 ∧
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p p0

/-- Any directly encoded term is in `EncodedSC`. -/
theorem encodedSC_of_encoded {n v : String} {p : Pattern}
    (h : EncodingMorphism.Encoded n v p) : EncodedSC n v p :=
  ⟨p, h, Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _⟩

/-- Encoding outputs are in `EncodedSC`. -/
theorem encode_is_EncodedSC (P : Process) (n v : String) :
    EncodedSC n v (encode P n v) :=
  encodedSC_of_encoded (EncodingMorphism.encode_is_Encoded P n v)

/-- `EncodedSC` is stable under left structural congruence transport. -/
theorem EncodedSC.of_sc {n v : String} {p q : Pattern}
    (hp : EncodedSC n v p)
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p q) :
    EncodedSC n v q := by
  rcases hp with ⟨p0, henc, hp0⟩
  refine ⟨p0, henc, ?_⟩
  exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.trans
    _ _ _ (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hsc) hp0

/-- Non-RF admin-layer sources used in π→ρ derived correspondence. -/
inductive AdminSource : Pattern → Prop where
  | nuListener (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
      AdminSource
        (rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda listenerBody]))
  | seedListener (x z v s : String) (listenerBody : Pattern) :
      AdminSource
        (rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda listenerBody]))
  | replicate (x y : Name) (P : Process) (n v : String) :
      AdminSource (encode (.replicate x y P) n v)

/-- Normalized bag COMM-source candidates used before backward reflection
constructs `AdminSource` witnesses. -/
inductive NormalizedBagCommCandidate : Pattern → Prop where
  | nuListener (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
      NormalizedBagCommCandidate
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nuListenerSource
          x P n v listenerBody)
  | seedListener (x z v s : String) (listenerBody : Pattern) :
      NormalizedBagCommCandidate
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nameServerListenerSource
          x z v s listenerBody)

/-- Inversion bridge: normalized COMM candidates map into the backward-reflection
source constructor family `AdminSource`. -/
theorem adminSource_of_normalizedBagCommCandidate {src : Pattern}
    (h : NormalizedBagCommCandidate src) : AdminSource src := by
  cases h with
  | nuListener x P n v listenerBody =>
      simpa
        [Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nuListenerSource] using
        (AdminSource.nuListener x P n v listenerBody)
  | seedListener x z v s listenerBody =>
      simpa
        [Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.nameServerListenerSource] using
        (AdminSource.seedListener x z v s listenerBody)

/-- Canonical admin targets paired with `AdminSource` terms. -/
inductive AdminCanonicalTarget : Pattern → Pattern → Prop where
  | nuListener (x : Name) (P : Process) (n v : String) (listenerBody : Pattern) :
      AdminCanonicalTarget
        (rhoPar (encode (.nu x P) n v) (.apply "PInput" [.fvar v, .lambda listenerBody]))
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none)
  | seedListener (x z v s : String) (listenerBody : Pattern) :
      AdminCanonicalTarget
        (rhoPar (nameServer x z v s) (.apply "PInput" [.fvar z, .lambda listenerBody]))
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none)
  | replicate (x y : Name) (P : Process) (n v : String) :
      AdminCanonicalTarget
        (encode (.replicate x y P) n v)
        (rhoPar
          (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v))
          (encode (.replicate x y P) n v))

/-- First backward theorem endpoint for non-RF admin sources:
derived progress to a canonical admin target up to derived weak bisimilarity. -/
theorem admin_source_forward_progress {N : Finset String} {src : Pattern}
    (hsrc : AdminSource src) :
    ∃ tgt canon, Nonempty (src ⇝ᵈ* tgt) ∧
      AdminCanonicalTarget src canon ∧
      tgt ≈ᵈ{N} canon := by
  cases hsrc with
  | nuListener x P n v listenerBody =>
      rcases forward_single_step_nu_listener_derived
          (N := N) x P n v listenerBody with ⟨tgt, hstep, hbisim⟩
      exact ⟨tgt,
        .collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.fvar n),
           rhoInput (.fvar n) x (encode P (n ++ "_" ++ n) v)] none,
        hstep, AdminCanonicalTarget.nuListener x P n v listenerBody, hbisim⟩
  | seedListener x z v s listenerBody =>
      rcases forward_single_step_nameServer_listener_derived
          (N := N) x z v s listenerBody with ⟨tgt, hstep, hbisim⟩
      exact ⟨tgt,
        .collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst listenerBody (.apply "PDrop" [.fvar s]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody x z v),
           dropOperation x] none,
        hstep, AdminCanonicalTarget.seedListener x z v s listenerBody, hbisim⟩
  | replicate x y P n v =>
      rcases forward_single_step_replicate_derived
          (N := N) x y P n v with ⟨tgt, hstep, hbisim⟩
      exact ⟨tgt,
        rhoPar
          (rhoInput (piNameToRhoName x) y (encode P (n ++ "_rep") v))
          (encode (.replicate x y P) n v),
        hstep, AdminCanonicalTarget.replicate x y P n v, hbisim⟩

/-- Weak backward reflection outcomes for non-RF admin sources.
The second branch is reserved for direct π-step reflection once proved. -/
inductive WeakBackwardOutcome (N : Finset String) (src : Pattern) : Prop where
  | adminProgress :
      (tgt : Pattern) →
      (canon : Pattern) →
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      AdminCanonicalTarget src canon →
      WeakRestrictedBisimD N tgt canon →
      WeakBackwardOutcome N src
  | piStep :
      (P P' : Process) →
      (tgt : Pattern) →
      src = encode P "n_init" "v_init" →
      Nonempty (P ⇝ P') →
      Nonempty (Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar src tgt) →
      WeakRestrictedBisimD N tgt (encode P' "n_init" "v_init") →
      WeakBackwardOutcome N src

/-- Weak backward reflection (non-RF admin layer):
an encoded/admin source reflects to administrative progress or a corresponding π-step.
Current closure is established by the administrative branch. -/
theorem weak_backward_reflection_nonRF_admin {N : Finset String} {src : Pattern}
    (hsrc : AdminSource src) :
    WeakBackwardOutcome N src := by
  rcases admin_source_forward_progress (N := N) hsrc with
    ⟨tgt, canon, hstep, hcanon, hbisim⟩
  exact WeakBackwardOutcome.adminProgress tgt canon hstep hcanon hbisim

/-- Direct encoded-COMM canary using the `piStep` backward-outcome branch. -/
theorem weak_backward_outcome_piStep_direct_encoded_comm_canary :
    WeakBackwardOutcome (∅ : Finset String)
      (encode (Process.par (Process.input "a" "y" .nil) (Process.output "a" "z"))
        "n_init" "v_init") := by
  have hrf :
      Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree
        (Process.par (Process.input "a" "y" Process.nil) (Process.output "a" "z")) := by
    simp [Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.RestrictionFree]
  have hsafe :
      Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.CommSafe
        (Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.ReducesRF.comm
          "a" "y" "z" Process.nil) := by
    have hyz : ("y" : Name) ≠ "z" := by decide
    have hb :
        Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.BarendregtFor
          "y" "z" Process.nil := by
      trivial
    exact ⟨hyz, hb⟩
  rcases forward_single_step_bisim
      (N := (∅ : Finset String))
      (Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation.ReducesRF.comm
        "a" "y" "z" Process.nil)
      hrf hsafe "n_init" "v_init" with
    ⟨tgt, hstepCore, _hbisimCore⟩
  have hpi :
      Nonempty
        ((Process.par (Process.input "a" "y" Process.nil) (Process.output "a" "z")) ⇝
          (Process.nil.substitute "y" "z")) := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduces.comm "a" "y" "z" Process.nil⟩
  have hstepDerived :
      Nonempty
        ((encode (Process.par (Process.input "a" "y" Process.nil) (Process.output "a" "z"))
          "n_init" "v_init") ⇝ᵈ* tgt) := by
    rcases hstepCore with ⟨hcore⟩
    exact
      ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesStar.toDerived hcore⟩
  exact WeakBackwardOutcome.piStep
    (Process.par (Process.input "a" "y" Process.nil) (Process.output "a" "z"))
    (Process.nil.substitute "y" "z")
    tgt rfl hpi hstepDerived
    (WeakRestrictedBisimD.empty tgt (encode (Process.nil.substitute "y" "z") "n_init" "v_init"))

/-- Nontrivial direct encoded-COMM canary:
uses a non-empty observation set and a reflexive derived bisim witness
rather than `WeakRestrictedBisimD.empty`. -/
theorem weak_backward_outcome_piStep_direct_encoded_comm_canary_nonempty :
    WeakBackwardOutcome ({ "a" } : Finset String)
      (encode (Process.par (Process.input "a" "y" .nil) (Process.output "a" "z"))
        "n_init" "v_init") := by
  let src : Pattern :=
    encode (Process.par (Process.input "a" "y" .nil) (Process.output "a" "z")) "n_init" "v_init"
  let tgt : Pattern := encode (Process.nil.substitute "y" "z") "n_init" "v_init"
  let preBag : Pattern :=
    .collection .hashBag
      [rhoInput (.fvar "a") "y" (encode .nil ("n_init" ++ "_L") "v_init"),
       rhoOutput (.fvar "a") (rhoDrop (.fvar "z"))] none
  let commBag : Pattern :=
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.commRedexShape
      (.fvar "a") (.apply "PDrop" [.fvar "z"])
      (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 "y" (encode .nil ("n_init" ++ "_L") "v_init"))
      []
  let postBag : Pattern :=
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.commTargetShape
      (.apply "PDrop" [.fvar "z"])
      (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 "y" (encode .nil ("n_init" ++ "_L") "v_init"))
      []
  have hsrcEq : src = preBag := by
    simp [src, preBag, encode, rhoPar, rhoInput, rhoOutput, rhoDrop, piNameToRhoName]
  have hdecomp :=
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.comm_decompose_encoded_source
      "a" "y" "z" .nil ("n_init" ++ "_L") "v_init" []
  have hpre :
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence src commBag := by
    simpa [preBag, commBag] using
      (show Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence preBag commBag from
        hdecomp.1)
  have hcomm : src ⇝ tgt := by
    have hcoreComm : commBag ⇝ postBag := Classical.choice hdecomp.2
    have hpost :
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence postBag tgt := by
      have hpostEq : postBag = .collection .hashBag [rhoNil] none := by
        simp [postBag, rhoNil,
          Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardNormalization.commTargetShape,
          Mettapedia.OSLF.MeTTaIL.Substitution.commSubst,
          Mettapedia.OSLF.MeTTaIL.Substitution.openBVar,
          Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar,
          encode]
      have htgtEq : tgt = rhoNil := by
        simp [tgt, Process.substitute, encode, rhoNil]
      simpa [hpostEq, htgtEq] using
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.par_singleton rhoNil)
    exact
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
        hpre hcoreComm hpost
  have hstepDerived : Nonempty (src ⇝ᵈ* tgt) := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesDerivedStar.single
      (.core hcomm)⟩
  have hpi :
      Nonempty
        ((Process.par (Process.input "a" "y" Process.nil) (Process.output "a" "z")) ⇝
          (Process.nil.substitute "y" "z")) := by
    exact ⟨Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduces.comm "a" "y" "z" Process.nil⟩
  exact WeakBackwardOutcome.piStep
    (Process.par (Process.input "a" "y" Process.nil) (Process.output "a" "z"))
    (Process.nil.substitute "y" "z")
    tgt hsrcEq hpi hstepDerived
    (WeakRestrictedBisimD.refl ({ "a" } : Finset String) tgt)

/-- Full non-RF admin correspondence (both directions, derived weak form):
forward wrappers plus backward reflection outcomes for ν/seed/replicate admin sources. -/
theorem full_nonRF_admin_correspondence_bidir {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern)
    (xr yr : Name) (Pr : Process) (n v : String) :
    (∃ Trep, Nonempty ((encode (.replicate xr yr Pr) n v) ⇝ᵈ* Trep) ∧
      Trep ≈ᵈ{N}
        (rhoPar
          (rhoInput (piNameToRhoName xr) yr (encode Pr (n ++ "_rep") v))
          (encode (.replicate xr yr Pr) n v))) ∧
    (∃ Tnu Tseed TrepNu,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      Nonempty
        ((.collection .hashBag
          [rhoPar (encode (.nu x P) "n_init" "v_init")
             (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]),
           rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
             (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]),
           encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, TrepNu] none)) ∧
      (.collection .hashBag [Tnu, Tseed] none ≡
        .collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N TrepNu
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"))) ∧
    WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    WeakBackwardOutcome N (encode (.replicate xr yr Pr) n v) := by
  rcases full_nonRF_forward_correspondence_derived
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v with
    ⟨hrepFwd, hnuFwd⟩
  have hbackNu :
      WeakBackwardOutcome N
        (rhoPar (encode (.nu x P) "n_init" "v_init")
          (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]))
      (AdminSource.nuListener x P "n_init" "v_init" nuListenerBody)
  have hbackSeed :
      WeakBackwardOutcome N
        (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
          (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]))
      (AdminSource.seedListener "ns_x" "ns_z" "v_init" "ns_seed" seedListenerBody)
  have hbackRep :
      WeakBackwardOutcome N (encode (.replicate xr yr Pr) n v) :=
    weak_backward_reflection_nonRF_admin
      (N := N) (src := encode (.replicate xr yr Pr) n v)
      (AdminSource.replicate xr yr Pr n v)
  exact ⟨hrepFwd, hnuFwd, hbackNu, hbackSeed, hbackRep⟩

/-- Backward reflection package for the combined non-RF administrative closure:
extracts explicit source components and encoded-image witnesses. -/
theorem backward_reflect_fullEncode_nu_admin_progress {N : Finset String}
    (x : Name) (P : Process) (nuListenerBody seedListenerBody : Pattern) :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      fullEncode (.nu x P) =
        rhoPar (encode (.nu x P) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      srcNu = rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      EncodedSC "n_init" "v_init" (encode (.nu x P) "n_init" "v_init") ∧
      EncodedSC "n_init" "v_init" srcRep ∧
      Nonempty
        ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
          (.collection .hashBag [Tnu, Tseed, Trep] none)) ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        (.collection .hashBag [Tnu, Tseed] none)
        (.collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD N Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst nuListenerBody (.fvar "n_init"),
           rhoInput (.fvar "n_init") x (encode P ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD N Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst seedListenerBody (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD N Trep
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")) := by
  let srcNu : Pattern := rhoPar (encode (.nu x P) "n_init" "v_init")
    (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])
  let srcSeed : Pattern := rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
    (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])
  let srcRep : Pattern := encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init"
  rcases fullEncode_nu_admin_progress_combined_derived
      (N := N) x P nuListenerBody seedListenerBody with
    ⟨Tnu, Tseed, Trep, hfull, htrace, hswap, hnu, hseed, hrep⟩
  refine ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hfull, rfl, rfl, rfl, ?_, ?_, htrace, hswap, hnu, hseed, hrep⟩
  · exact encode_is_EncodedSC (.nu x P) "n_init" "v_init"
  · simpa [srcRep] using
      (encode_is_EncodedSC (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")

/-- Concrete backward-stage canary. -/
theorem backward_reflect_fullEncode_nu_admin_progress_canary :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      fullEncode (.nu "x" .nil) =
        rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      srcNu = rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda rhoNil]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda rhoNil]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      Nonempty ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
        (.collection .hashBag [Tnu, Tseed, Trep] none)) := by
  rcases backward_reflect_fullEncode_nu_admin_progress
      (N := (∅ : Finset String)) "x" .nil rhoNil rhoNil with
    ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hfull, hnuEq, hseedEq, hrepEq, _hEncNu, _hEncRep, htrace, _hswap, _hnu, _hseed, _hrep⟩
  exact ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hfull, hnuEq, hseedEq, hrepEq, htrace⟩

/-- Nontrivial backward-stage canary with concrete non-`rhoNil` listeners. -/
theorem backward_reflect_fullEncode_nu_admin_progress_canary_nontrivial :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      srcNu = rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda (.apply "PDrop" [.fvar "k"])]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda (.apply "NQuote" [.fvar "m"])]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      Nonempty ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
        (.collection .hashBag [Tnu, Tseed, Trep] none)) := by
  rcases backward_reflect_fullEncode_nu_admin_progress
      (N := (∅ : Finset String)) "x" .nil
      (.apply "PDrop" [.fvar "k"]) (.apply "NQuote" [.fvar "m"]) with
    ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, _hfull, hnuEq, hseedEq, hrepEq,
      _hEncNu, _hEncRep, htrace, _hswap, _hnu, _hseed, _hrep⟩
  exact ⟨srcNu, srcSeed, srcRep, Tnu, Tseed, Trep, hnuEq, hseedEq, hrepEq, htrace⟩

/-- Strong nontrivial backward-stage canary:
concrete listeners with encoded-image witnesses and endpoint bisim outputs. -/
theorem backward_reflect_fullEncode_nu_admin_progress_canary_nontrivial_full :
    ∃ srcNu srcSeed srcRep Tnu Tseed Trep,
      fullEncode (.nu "x" .nil) =
        rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
          (nameServer "ns_x" "ns_z" "v_init" "ns_seed") ∧
      srcNu = rhoPar (encode (.nu "x" .nil) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda (.apply "PDrop" [.fvar "k"])]) ∧
      srcSeed = rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda (.apply "NQuote" [.fvar "m"])]) ∧
      srcRep = encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init" ∧
      EncodedSC "n_init" "v_init" (encode (.nu "x" .nil) "n_init" "v_init") ∧
      EncodedSC "n_init" "v_init" srcRep ∧
      Nonempty ((.collection .hashBag [srcNu, srcSeed, srcRep] none) ⇝ᵈ*
        (.collection .hashBag [Tnu, Tseed, Trep] none)) ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        (.collection .hashBag [Tnu, Tseed] none)
        (.collection .hashBag [Tseed, Tnu] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Tnu
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (.apply "PDrop" [.fvar "k"]) (.fvar "n_init"),
           rhoInput (.fvar "n_init") "x" (encode .nil ("n_init" ++ "_" ++ "n_init") "v_init")] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Tseed
        (.collection .hashBag
          [Mettapedia.OSLF.MeTTaIL.Substitution.commSubst (.apply "NQuote" [.fvar "m"]) (.apply "PDrop" [.fvar "ns_seed"]),
           rhoReplicate (Mettapedia.Languages.ProcessCalculi.PiCalculus.nameServerBody "ns_x" "ns_z" "v_init"),
           dropOperation "ns_x"] none) ∧
      WeakRestrictedBisimD (∅ : Finset String) Trep
        (rhoPar
          (rhoInput (piNameToRhoName "ns_x") "_drop" (encode .nil ("n_init" ++ "_rep") "v_init"))
          (encode (.replicate "ns_x" "_drop" .nil) "n_init" "v_init")) := by
  simpa using
    (backward_reflect_fullEncode_nu_admin_progress
      (N := (∅ : Finset String)) "x" .nil
      (.apply "PDrop" [.fvar "k"]) (.apply "NQuote" [.fvar "m"]))

end Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection
