import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsInf
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierSemantics

/-!
# Fuzzy Domain Quantifiers

Fuzzy-domain lift for the infinitary `[0,1]`-valued quantifier surface.

The basic idea follows the Dvorak-Holcapek fuzzy-universe/fuzzy-domain line:
the quantifier acts over a pair `(M, C)`, where `C` is a fuzzy domain profile on
the crisp carrier `M`, and arguments are evaluated only through their
restriction to `C`.

This file provides:

- fuzzy-domain restriction by pointwise `min`
- "living on the domain" equalities and monotonicity lemmas
- relativized unary/binary forms for the proxy-cut infinitary semantics
- relativized unary/binary forms for the Choquet semantics
-/

namespace Mettapedia.Logic.PLNFirstOrder

open scoped unitInterval

variable {U : Type*} [MeasurableSpace U]

/-- Pointwise restriction of a fuzzy profile to a fuzzy domain profile. -/
def domainRestrict (C A : FuzzyProfile U) : FuzzyProfile U :=
  ⟨fun u => min (C u) (A u)⟩

/-- Equality of profiles with respect to a fuzzy domain: only the restricted
part matters. -/
def eqOnDomain (C A B : FuzzyProfile U) : Prop :=
  domainRestrict C A = domainRestrict C B

section DomainRestrictionLemmas

variable {U : Type*}

theorem domainRestrict_apply (C A : FuzzyProfile U) (u : U) :
    domainRestrict C A u = min (C u) (A u) := rfl

theorem domainRestrict_assoc
    (C A B : FuzzyProfile U) :
    domainRestrict C (domainRestrict A B) =
      domainRestrict (domainRestrict C A) B := by
  cases C
  cases A
  cases B
  simp [domainRestrict, min_assoc]

theorem domainRestrict_idem
    (C : FuzzyProfile U) :
    domainRestrict C C = C := by
  cases C
  simp [domainRestrict]

theorem domainRestrict_constOne
    (C : FuzzyProfile U) :
    domainRestrict C (FuzzyProfile.const (U := U) (1 : I)) = C := by
  cases C
  refine congrArg FuzzyProfile.mk ?_
  funext u
  exact min_eq_left (unitInterval.le_one _)

theorem domainRestrict_le_right
    (C A : FuzzyProfile U) (u : U) :
    domainRestrict C A u ≤ A u := by
  simp [domainRestrict]

theorem domainRestrict_mono_right
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u) :
    ∀ u, domainRestrict C A u ≤ domainRestrict C B u := by
  intro u
  simp [domainRestrict, hAB u]

theorem eqOnDomain_refl
    (C A : FuzzyProfile U) :
    eqOnDomain C A A := rfl

theorem eqOnDomain_symm
    {C A B : FuzzyProfile U} :
    eqOnDomain C A B → eqOnDomain C B A := by
  intro h
  simpa [eqOnDomain] using h.symm

theorem eqOnDomain_trans
    {C A B D : FuzzyProfile U} :
    eqOnDomain C A B → eqOnDomain C B D → eqOnDomain C A D := by
  intro hAB hBD
  simpa [eqOnDomain] using hAB.trans hBD

end DomainRestrictionLemmas

/-- Proxy-cut existential score restricted to a fuzzy domain. -/
def fuzzyExistsOnDomainScoreInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : I :=
  fuzzyExistsScoreInf p ν (domainRestrict C B)

/-- Proxy-cut interval truth restricted to a fuzzy domain. -/
def fuzzyIntervalOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  fuzzyIntervalHoldsInf p ν (domainRestrict C B)

/-- Proxy-cut universal truth restricted to a fuzzy domain. -/
def fuzzyForAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  fuzzyForAllHoldsInf p ν (domainRestrict C B)

/-- Proxy-cut existential truth restricted to a fuzzy domain. -/
def fuzzyThereExistsOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  fuzzyThereExistsHoldsInf p ν (domainRestrict C B)

/-- Binary "all" obtained by relativizing the unary proxy-cut universal semantics
through the fuzzy domain profile. -/
def fuzzyAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  fuzzyForAllOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B)

/-- Binary "some" obtained by relativizing the unary proxy-cut existential semantics
through the fuzzy domain profile. -/
def fuzzySomeOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  fuzzyThereExistsOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B)

theorem fuzzyExistsOnDomainScoreInf_eq_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyExistsOnDomainScoreInf p ν C A = fuzzyExistsOnDomainScoreInf p ν C B := by
  simpa [fuzzyExistsOnDomainScoreInf] using
    congrArg (fun t => fuzzyExistsScoreInf p ν t) hAB

theorem fuzzyIntervalOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyIntervalOnDomainHoldsInf p ν C A ↔ fuzzyIntervalOnDomainHoldsInf p ν C B := by
  simpa [fuzzyIntervalOnDomainHoldsInf] using
    (show fuzzyIntervalHoldsInf p ν (domainRestrict C A) ↔
        fuzzyIntervalHoldsInf p ν (domainRestrict C B) by
      rw [hAB])

theorem fuzzyForAllOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyForAllOnDomainHoldsInf p ν C A ↔ fuzzyForAllOnDomainHoldsInf p ν C B := by
  simpa [fuzzyForAllOnDomainHoldsInf] using
    (show fuzzyForAllHoldsInf p ν (domainRestrict C A) ↔
        fuzzyForAllHoldsInf p ν (domainRestrict C B) by
      rw [hAB])

theorem fuzzyThereExistsOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    fuzzyThereExistsOnDomainHoldsInf p ν C A ↔
      fuzzyThereExistsOnDomainHoldsInf p ν C B := by
  simpa [fuzzyThereExistsOnDomainHoldsInf] using
    (show fuzzyThereExistsHoldsInf p ν (domainRestrict C A) ↔
        fuzzyThereExistsHoldsInf p ν (domainRestrict C B) by
      rw [hAB])

theorem fuzzyExistsOnDomainScoreInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u) :
    fuzzyExistsOnDomainScoreInf p ν C A ≤ fuzzyExistsOnDomainScoreInf p ν C B := by
  exact fuzzyExistsScoreInf_mono_of_pointwise p ν
    (domainRestrict C A) (domainRestrict C B) (domainRestrict_mono_right C A B hAB)

theorem fuzzyForAllOnDomainHoldsInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u)
    (hA : fuzzyForAllOnDomainHoldsInf p ν C A) :
    fuzzyForAllOnDomainHoldsInf p ν C B := by
  exact fuzzyForAllHoldsInf_mono_of_pointwise p ν
    (domainRestrict C A) (domainRestrict C B) (domainRestrict_mono_right C A B hAB) hA

theorem fuzzyAllOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    fuzzyAllOnDomainHoldsInf p ν C A B ↔
      fuzzyForAllOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  Iff.rfl

theorem fuzzySomeOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    fuzzySomeOnDomainHoldsInf p ν C A B ↔
      fuzzyThereExistsOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  Iff.rfl

/-- Choquet score restricted to a fuzzy domain. -/
noncomputable def choquetOnDomainScoreInf
    (ν : FuzzyCapacity U) (C B : FuzzyProfile U) : I :=
  choquetScoreInf ν (domainRestrict C B)

/-- Choquet interval truth restricted to a fuzzy domain. -/
def choquetIntervalOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  choquetIntervalHoldsInf p ν (domainRestrict C B)

/-- Choquet universal truth restricted to a fuzzy domain. -/
def choquetForAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  choquetForAllHoldsInf p ν (domainRestrict C B)

/-- Choquet existential truth restricted to a fuzzy domain. -/
def choquetThereExistsOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C B : FuzzyProfile U) : Prop :=
  choquetThereExistsHoldsInf p ν (domainRestrict C B)

/-- Binary Choquet "all" by relativization through a fuzzy domain profile. -/
def choquetAllOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  choquetForAllOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B)

/-- Binary Choquet "some" by relativization through a fuzzy domain profile. -/
def choquetSomeOnDomainHoldsInf
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) : Prop :=
  choquetThereExistsOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B)

theorem choquetOnDomainScoreInf_eq_of_eqOnDomain
    (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetOnDomainScoreInf ν C A = choquetOnDomainScoreInf ν C B := by
  simpa [choquetOnDomainScoreInf] using
    congrArg (fun t => choquetScoreInf ν t) hAB

theorem choquetIntervalOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetIntervalOnDomainHoldsInf p ν C A ↔
      choquetIntervalOnDomainHoldsInf p ν C B := by
  have hScoreEq : choquetScoreInf ν (domainRestrict C A) =
      choquetScoreInf ν (domainRestrict C B) := by
    simpa [choquetOnDomainScoreInf] using choquetOnDomainScoreInf_eq_of_eqOnDomain ν hAB
  simpa [choquetIntervalOnDomainHoldsInf] using
    choquetIntervalHoldsInf_iff_of_eq p ν (domainRestrict C A) (domainRestrict C B) hScoreEq

theorem choquetForAllOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetForAllOnDomainHoldsInf p ν C A ↔
      choquetForAllOnDomainHoldsInf p ν C B := by
  have hScoreEq : choquetScoreInf ν (domainRestrict C A) =
      choquetScoreInf ν (domainRestrict C B) := by
    simpa [choquetOnDomainScoreInf] using choquetOnDomainScoreInf_eq_of_eqOnDomain ν hAB
  unfold choquetForAllOnDomainHoldsInf choquetForAllHoldsInf
  simp [hScoreEq]

theorem choquetThereExistsOnDomainHoldsInf_iff_of_eqOnDomain
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    {C A B : FuzzyProfile U}
    (hAB : eqOnDomain C A B) :
    choquetThereExistsOnDomainHoldsInf p ν C A ↔
      choquetThereExistsOnDomainHoldsInf p ν C B := by
  have hScoreEq :
      choquetScoreInf ν (FuzzyProfile.compl (domainRestrict C A)) =
        choquetScoreInf ν (FuzzyProfile.compl (domainRestrict C B)) := by
    simpa using congrArg (fun t => choquetScoreInf ν (FuzzyProfile.compl t)) hAB
  unfold choquetThereExistsOnDomainHoldsInf choquetThereExistsHoldsInf
  simp [hScoreEq]

theorem choquetOnDomainScoreInf_mono_of_pointwise
    (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u) :
    choquetOnDomainScoreInf ν C A ≤ choquetOnDomainScoreInf ν C B := by
  exact choquetScoreInf_mono ν
    (domainRestrict C A) (domainRestrict C B) (domainRestrict_mono_right C A B hAB)

theorem choquetForAllOnDomainHoldsInf_mono_of_pointwise
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U)
    (hAB : ∀ u, A u ≤ B u)
    (hA : choquetForAllOnDomainHoldsInf p ν C A) :
    choquetForAllOnDomainHoldsInf p ν C B := by
  unfold choquetForAllOnDomainHoldsInf at *
  exact le_trans hA (choquetOnDomainScoreInf_mono_of_pointwise ν C A B hAB)

theorem choquetAllOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    choquetAllOnDomainHoldsInf p ν C A B ↔
      choquetForAllOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  Iff.rfl

theorem choquetSomeOnDomainHoldsInf_relativized
    (p : FuzzyQuantifierParamsInf) (ν : FuzzyCapacity U)
    (C A B : FuzzyProfile U) :
    choquetSomeOnDomainHoldsInf p ν C A B ↔
      choquetThereExistsOnDomainHoldsInf p ν (domainRestrict C A) (domainRestrict A B) :=
  Iff.rfl

end Mettapedia.Logic.PLNFirstOrder
