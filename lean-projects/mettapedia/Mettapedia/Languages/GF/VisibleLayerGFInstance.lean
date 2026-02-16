import Mettapedia.Languages.GF.VisibleLayer

/-!
# GF-Specific Visible Layer Instance

Concrete `NPReplacer` for the GF RGL grammar. Recognizes NP constructors
(`DetCN`, `MassNP`, `UsePN`, `UsePron`) and replaces them with quantifier
variable placeholders `⊛NPVar(q)`.
-/

namespace Mettapedia.Languages.GF.VisibleLayerGFInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.GF.VisibleLayer

/-- Check if a pattern is a recognized NP constructor. -/
def isNPConstructor : Pattern → Bool
  | .apply "DetCN" [_, _] => true
  | .apply "MassNP" [_] => true
  | .apply "UsePN" [_] => true
  | .apply "UsePron" [_] => true
  | _ => false

/-- NPVar placeholder: `⊛NPVar(q)` encodes a quantifier variable in the term tree. -/
def npVar (q : String) : Pattern :=
  .apply "⊛NPVar" [.apply q []]

/-- Replace first NP in a list of patterns. Returns modified list or none. -/
def replaceFirstNPInList (q : String) : List Pattern → Option (List Pattern)
  | [] => none
  | p :: rest =>
    if isNPConstructor p then
      some (npVar q :: rest)
    else
      match p with
      | .apply f args =>
        match replaceFirstNPInList q args with
        | some args' => some (.apply f args' :: rest)
        | none =>
          match replaceFirstNPInList q rest with
          | some rest' => some (p :: rest')
          | none => none
      | _ =>
        match replaceFirstNPInList q rest with
        | some rest' => some (p :: rest')
        | none => none

/-- Replace the first NP constructor found in the pattern tree with `⊛NPVar(q)`. -/
def replaceFirstNP (t : Pattern) (q : String) : Option Pattern :=
  if isNPConstructor t then
    some (npVar q)
  else
    match t with
    | .apply f args =>
      match replaceFirstNPInList q args with
      | some args' => some (.apply f args')
      | none => none
    | _ => none

/-- GF-specific NP replacer. -/
def gfNPReplacer : NPReplacer where
  replaceNPWithVar := replaceFirstNP

/-- GF visible layer configuration. -/
def gfVisibleCfg : VisibleCfg := ⟨gfNPReplacer⟩

/-! ## Verification -/

/-- DetCN(the, cat) is recognized as an NP. -/
example : isNPConstructor (.apply "DetCN" [.apply "the_Det" [], .apply "cat_CN" []]) = true :=
  rfl

/-- UseN(cat) is NOT an NP. -/
example : isNPConstructor (.apply "UseN" [.apply "cat_N" []]) = false :=
  rfl

/-- Replacing DetCN yields NPVar. -/
example : replaceFirstNP
    (.apply "DetCN" [.apply "every_Det" [], .apply "student_CN" []])
    "q1" = some (npVar "q1") := by
  simp [replaceFirstNP, isNPConstructor, npVar]

/-- Replacing inside PredVP(DetCN(...), UseV(...)) finds the nested NP. -/
example : replaceFirstNP
    (.apply "PredVP" [
      .apply "DetCN" [.apply "every_Det" [], .apply "student_CN" []],
      .apply "UseV" [.apply "sleep_V" []]])
    "q1" = some (.apply "PredVP" [
      npVar "q1",
      .apply "UseV" [.apply "sleep_V" []]]) := by
  simp [replaceFirstNP, replaceFirstNPInList, isNPConstructor, npVar]

/-- No NP in a bare verb → none. -/
example : replaceFirstNP (.apply "UseV" [.apply "sleep_V" []]) "q1" = none := by
  simp [replaceFirstNP, replaceFirstNPInList, isNPConstructor]

end Mettapedia.Languages.GF.VisibleLayerGFInstance
