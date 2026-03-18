import Mettapedia.Languages.GF.HandCrafted.Abstract
import Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses

namespace Mettapedia.Languages.GF.PaperAmbiguityPGFBridge

open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses

private def mkLeaf (name cat : String) : AbstractNode :=
  .leaf name (.base cat)

private def mkApp1 (fname d1 res : String) (a1 : AbstractNode) : AbstractNode :=
  .apply { name := fname, type := .arrow (.base d1) (.base res) } [a1]

private def mkApp2 (fname d1 d2 res : String) (a1 a2 : AbstractNode) : AbstractNode :=
  .apply { name := fname, type := .arrow (.base d1) (.arrow (.base d2) (.base res)) } [a1, a2]

private def mkApp3 (fname d1 d2 d3 res : String) (a1 a2 a3 : AbstractNode) : AbstractNode :=
  .apply {
      name := fname
      type := .arrow (.base d1) (.arrow (.base d2) (.arrow (.base d3) (.base res)))
    } [a1, a2, a3]

private def presTemp : AbstractNode :=
  mkApp2 "TTAnt" "Tense" "Ant" "Temp"
    (mkLeaf "TPres" "Tense") (mkLeaf "ASimul" "Ant")

private def posPol : AbstractNode := mkLeaf "PPos" "Pol"
private def johnNPTree : AbstractNode := mkApp1 "UsePN" "PN" "NP" (mkLeaf "john_PN" "PN")
private def annaNPTree : AbstractNode := mkApp1 "UsePN" "PN" "NP" (mkLeaf "anna_PN" "PN")
private def manCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "man_N" "N")
private def babyCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "baby_N" "N")
private def telescopeCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "telescope_N" "N")
private def cribCNTree : AbstractNode := mkApp1 "UseN" "N" "CN" (mkLeaf "crib_N" "N")
private def theManTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") manCNTree
private def theBabyTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") babyCNTree
private def theTelescopeTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") telescopeCNTree
private def theCribTree : AbstractNode :=
  mkApp2 "DetCN" "Det" "CN" "NP" (mkLeaf "the_Det" "Det") cribCNTree
private def withTelescopeAdvTree : AbstractNode :=
  mkApp2 "PrepNP" "Prep" "NP" "Adv" (mkLeaf "with_Prep" "Prep") theTelescopeTree
private def inCribAdvTree : AbstractNode :=
  mkApp2 "PrepNP" "Prep" "NP" "Adv" (mkLeaf "in_Prep" "Prep") theCribTree

/-- VP-attachment reading: John [sees the man] [with the telescope]. -/
def telescopeVPAttachmentPresTree : AbstractNode :=
  mkApp3 "UseCl" "Temp" "Pol" "Cl" "S" presTemp posPol
    (mkApp2 "PredVP" "NP" "VP" "Cl"
      johnNPTree
      (mkApp2 "AdvVP" "VP" "Adv" "VP"
        (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
          (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "see_V2" "V2"))
          theManTree)
        withTelescopeAdvTree))

/-- NP-attachment reading: John sees [the man with the telescope]. -/
def telescopeNPAttachmentPresTree : AbstractNode :=
  mkApp3 "UseCl" "Temp" "Pol" "Cl" "S" presTemp posPol
    (mkApp2 "PredVP" "NP" "VP" "Cl"
      johnNPTree
      (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
        (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "see_V2" "V2"))
        (mkApp2 "DetCN" "Det" "CN" "NP"
          (mkLeaf "the_Det" "Det")
          (mkApp2 "AdvCN" "CN" "Adv" "CN" manCNTree withTelescopeAdvTree))))

/-- VP-attachment reading: Anna [dresses the baby] [in the crib]. -/
def annaVPAttachmentPresTree : AbstractNode :=
  mkApp3 "UseCl" "Temp" "Pol" "Cl" "S" presTemp posPol
    (mkApp2 "PredVP" "NP" "VP" "Cl"
      annaNPTree
      (mkApp2 "AdvVP" "VP" "Adv" "VP"
        (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
          (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "dress_V2" "V2"))
          theBabyTree)
        inCribAdvTree))

/-- NP-attachment reading: Anna dresses [the baby in the crib]. -/
def annaNPAttachmentPresTree : AbstractNode :=
  mkApp3 "UseCl" "Temp" "Pol" "Cl" "S" presTemp posPol
    (mkApp2 "PredVP" "NP" "VP" "Cl"
      annaNPTree
      (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
        (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "dress_V2" "V2"))
        (mkApp2 "DetCN" "Det" "CN" "NP"
          (mkLeaf "the_Det" "Det")
          (mkApp2 "AdvCN" "CN" "Adv" "CN" babyCNTree inCribAdvTree))))


theorem english_telescope_recovered :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishTelescopeRecovered =
      [telescopeVPAttachmentPresTree, telescopeNPAttachmentPresTree] := by
  rfl

theorem english_anna_recovered :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishAnnaRecovered =
      [annaVPAttachmentPresTree, annaNPAttachmentPresTree] := by
  rfl

theorem czech_telescope_recovered :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechTelescopeRecovered =
      [telescopeVPAttachmentPresTree, telescopeNPAttachmentPresTree] := by
  rfl

theorem czech_anna_recovered :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechAnnaRecovered =
      [annaVPAttachmentPresTree, annaNPAttachmentPresTree] := by
  rfl

theorem english_czech_telescope_recovered_equal :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishTelescopeRecovered =
      Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechTelescopeRecovered := by
  rw [english_telescope_recovered, czech_telescope_recovered]

theorem english_czech_anna_recovered_equal :
    Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.englishAnnaRecovered =
      Mettapedia.Languages.GF.Generated.PaperAmbiguityPGFWitnesses.czechAnnaRecovered := by
  rw [english_anna_recovered, czech_anna_recovered]


end Mettapedia.Languages.GF.PaperAmbiguityPGFBridge
