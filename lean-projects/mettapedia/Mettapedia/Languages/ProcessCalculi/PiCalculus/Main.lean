import Mettapedia.Languages.ProcessCalculi.PiCalculus.Syntax
import Mettapedia.Languages.ProcessCalculi.PiCalculus.StructuralCongruence
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Reduction
import Mettapedia.Languages.ProcessCalculi.PiCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingMorphism
import Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection

/-!
# π-Calculus Formalization

Main entry point that re-exports all π-calculus modules.

## Contents
- Syntax: Process syntax and names
- StructuralCongruence: α-equivalence and ≡ relation
- Reduction: Operational semantics
- MultiStep: Reflexive-transitive closure of reduction

## Future Work
- Bisimulation: Behavioral equivalence
- RhoEncoding: Encoding π → ρ (Lybech 2022)
- SeparationTheorem: Proof that π ⊄ ρ (Lybech 2022, Theorem 1)
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

/-- Umbrella re-export theorem: non-RF administrative correspondence
combining forward and backward π→ρ endpoints. -/
theorem nonRF_admin_correspondence_umbrella {N : Finset String}
    (x : Name) (P : Process)
    (nuListenerBody seedListenerBody : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
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
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (encode (.nu x P) "n_init" "v_init")
        (.apply "PInput" [.fvar "v_init", .lambda nuListenerBody])) ∧
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection.WeakBackwardOutcome N
      (rhoPar (nameServer "ns_x" "ns_z" "v_init" "ns_seed")
        (.apply "PInput" [.fvar "ns_z", .lambda seedListenerBody])) ∧
    Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection.WeakBackwardOutcome N
      (encode (.replicate xr yr Pr) n v) := by
  simpa using
    (Mettapedia.Languages.ProcessCalculi.PiCalculus.BackwardAdminReflection.full_nonRF_admin_correspondence_bidir
      (N := N) x P nuListenerBody seedListenerBody xr yr Pr n v)

end Mettapedia.Languages.ProcessCalculi.PiCalculus
