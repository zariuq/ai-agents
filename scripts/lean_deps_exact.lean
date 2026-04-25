import Lean
import Lean.Util.FoldConsts

open Lean

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def Expr.getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstants' (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstants' ++ match c.value? with
  | some v => v.getUsedConstants'
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .opaqueInfo val => val.value.getUsedConstants'
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

end ConstantInfo

def nameSetToSortedArray (s : NameSet) : Array Name :=
  let arr := s.fold (fun acc name => acc.push name) #[]
  arr.qsort Name.quickLt

def jsonStringArray (xs : Array String) : Json :=
  Json.arr <| xs.map Json.str

def nameHasSorryComponent (name : Name) : Bool :=
  name.components.any fun comp => comp == `sorryAx || comp == `admitAx

def infoUsesSorry (info : ConstantInfo) : Bool :=
  info.getUsedConstants'.any nameHasSorryComponent

def readModuleLines (moduleName : Name) : IO (Array String) := do
  let oleanFile ← findOLean moduleName
  unless (← oleanFile.pathExists) do
    throw <| IO.userError s!"object file '{oleanFile}' of module {moduleName} does not exist"

  let mut fileNames := #[oleanFile]
  let serverFile := OLeanLevel.server.adjustFileName oleanFile
  if (← serverFile.pathExists) then
    fileNames := fileNames.push serverFile
    let privateFile := OLeanLevel.private.adjustFileName oleanFile
    if (← privateFile.pathExists) then
      fileNames := fileNames.push privateFile

  let parts ← readModuleDataParts fileNames
  let some (mod, _) := parts.back? | unreachable!

  let mut lines := #[]
  for name in mod.constNames, info in mod.constants do
    let deps := nameSetToSortedArray info.getUsedConstants' |>.map toString
    let obj := Json.mkObj
      [ ("module", Json.str (toString moduleName))
      , ("name", Json.str (toString name))
      , ("deps", jsonStringArray deps)
      , ("uses_sorry", Json.bool (infoUsesSorry info))
      ]
    lines := lines.push obj.compress

  parts.forM fun (_, region) => region.free
  return lines

def parseModuleName (arg : String) : Name :=
  Id.run do
    let mut acc := Name.anonymous
    for part in arg.splitOn "." do
      if !part.isEmpty then
        acc := acc.str part
    acc

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    throw <| IO.userError "usage: lake env lean --run ~/claude/scripts/lean_deps_exact.lean Module.Name ..."

  for arg in args do
    let moduleName := parseModuleName arg
    let lines ← readModuleLines moduleName
    for line in lines do
      IO.println line
  return 0
