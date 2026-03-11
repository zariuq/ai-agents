import Mettapedia.Languages.MeTTa.PureCheckingExtensions
import Mettapedia.Languages.MeTTa.InductiveCertificateInterface
import Mettapedia.Languages.MeTTa.InductiveRecursorContract

/-!
# Ordinary-Family Implementation Seeds

This file packages the strongest honest ordinary-family implementation-facing
objects available today without pretending that `PureKernel` already contains
inductive constructors or recursor reduction.

Each seed ties together:
- the checked ordinary-family wrapper above `PureCheckingService`,
- the explicit recursor contract for that family, and
- one current runtime-friendly constructor overlap bridge.
-/

namespace Mettapedia.Languages.MeTTa

/-- Strongest honest implementation-facing seed for one starter ordinary
family at the current architecture level. -/
structure OrdinaryFamilyImplementationSeed where
  checkedFamily : CheckedOrdinaryFamily
  overlapBridge : InductiveOverlapBridge
  recursorContract : FamilyRecursorContract
  familyName_eq :
    checkedFamily.extension.declaration.familyName = overlapBridge.familyName
  recursorName_eq :
    checkedFamily.extension.declaration.recursorName = recursorContract.recursorName
  overlapClass_eq :
    checkedFamily.service.overlapClass = OverlapClass.artifactOnly
  runtimeTranslatable :
    morkTranslatable overlapBridge.runtimeCandidate.artifact.pattern = true

def unitFamilyImplementationSeed : OrdinaryFamilyImplementationSeed :=
  { checkedFamily := checkedUnitFamily
    overlapBridge := unitOverlapBridge
    recursorContract := unitRecursorContract
    familyName_eq := by
      simpa [InductiveOverlapBridge.familyName] using checkedUnitFamily_familyName
    recursorName_eq := by
      simpa [CheckedOrdinaryFamily.recursorContract] using unitRecursorContract_name
    overlapClass_eq := by
      simpa [checkedUnitFamily, checkOrdinaryFamilyCanonical,
        PureCheckingBoundary.checkOrdinaryFamily, pureCheckingBoundary]
    runtimeTranslatable := unitOverlapBridge_runtimeTranslatable }

def boolFamilyImplementationSeed : OrdinaryFamilyImplementationSeed :=
  { checkedFamily := checkedBoolFamily
    overlapBridge := boolTrueOverlapBridge
    recursorContract := boolRecursorContract
    familyName_eq := by
      simpa [InductiveOverlapBridge.familyName] using checkedBoolFamily_familyName
    recursorName_eq := by
      simpa [CheckedOrdinaryFamily.recursorContract] using boolRecursorContract_name
    overlapClass_eq := by
      simpa [checkedBoolFamily, checkOrdinaryFamilyCanonical,
        PureCheckingBoundary.checkOrdinaryFamily, pureCheckingBoundary]
    runtimeTranslatable := boolTrueOverlapBridge_runtimeTranslatable }

def natFamilyImplementationSeed : OrdinaryFamilyImplementationSeed :=
  { checkedFamily := checkedNatFamily
    overlapBridge := natZeroOverlapBridge
    recursorContract := natRecursorContract
    familyName_eq := by
      simpa [InductiveOverlapBridge.familyName] using checkedNatFamily_familyName
    recursorName_eq := by
      simpa [CheckedOrdinaryFamily.recursorContract] using natRecursorContract_name
    overlapClass_eq := by
      simpa [checkedNatFamily, checkOrdinaryFamilyCanonical,
        PureCheckingBoundary.checkOrdinaryFamily, pureCheckingBoundary]
    runtimeTranslatable := natZeroOverlapBridge_runtimeTranslatable }

theorem unitFamilyImplementationSeed_family :
    unitFamilyImplementationSeed.checkedFamily.extension.declaration.familyName = "Unit" := by
  exact checkedUnitFamily_familyName

theorem boolFamilyImplementationSeed_family :
    boolFamilyImplementationSeed.checkedFamily.extension.declaration.familyName = "Bool" := by
  exact checkedBoolFamily_familyName

theorem natFamilyImplementationSeed_family :
    natFamilyImplementationSeed.checkedFamily.extension.declaration.familyName = "Nat" := by
  exact checkedNatFamily_familyName

theorem unitFamilyImplementationSeed_recursor :
    unitFamilyImplementationSeed.recursorContract.recursorName = "Unit.rec" := by
  rfl

theorem boolFamilyImplementationSeed_recursor :
    boolFamilyImplementationSeed.recursorContract.recursorName = "Bool.rec" := by
  rfl

theorem natFamilyImplementationSeed_recursor :
    natFamilyImplementationSeed.recursorContract.recursorName = "Nat.rec" := by
  rfl

theorem starterOrdinaryFamilySeeds_still_artifactOnly :
    unitFamilyImplementationSeed.overlapClass_eq ∧
      boolFamilyImplementationSeed.overlapClass_eq ∧
      natFamilyImplementationSeed.overlapClass_eq := by
  constructor
  · exact unitFamilyImplementationSeed.overlapClass_eq
  constructor
  · exact boolFamilyImplementationSeed.overlapClass_eq
  · exact natFamilyImplementationSeed.overlapClass_eq

end Mettapedia.Languages.MeTTa
