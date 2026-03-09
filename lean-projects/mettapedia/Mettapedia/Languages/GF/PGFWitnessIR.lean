import Mettapedia.Languages.GF.Abstract

namespace Mettapedia.Languages.GF.PGFWitnessIR

open Mettapedia.Languages.GF.Abstract

inductive ExportedTree where
  | node : String → List ExportedTree → ExportedTree
  deriving Repr

structure SurfaceWitness where
  label : String
  language : String
  surface : String
  parses : List ExportedTree
  deriving Repr

structure WitnessBundle where
  grammar : String
  usedFunctions : List String
  witnesses : List SurfaceWitness
  deriving Repr

namespace ExportedTree

mutual
  def buildApply? (f : FunctionSig) (args : List ExportedTree) : Option AbstractNode := do
    let converted ← args.mapM toAbstractNode?
    if converted.length = FunctionSig.arity f then
      some (.apply f converted)
    else
      none

  /-- Convert a GF/PGF-exported application tree into the mettapedia abstract-node encoding. -/
  def toAbstractNode? : ExportedTree → Option AbstractNode
    | .node name args => do
        let f ← FunctionSig.findByName? name
        if args.isEmpty then
          if FunctionSig.arity f = 0 then
            some (.leaf name (FunctionSig.resultCategory f.type))
          else
            none
        else
          buildApply? f args
end

/-- Collect all abstract function names appearing in the exported tree. -/
def functionNames : ExportedTree → List String
  | .node name args =>
      name :: (args.foldr (fun arg acc => functionNames arg ++ acc) [])

end ExportedTree

namespace SurfaceWitness

/-- Successfully recovered abstract trees from the exported parse list. -/
def recoveredParses (w : SurfaceWitness) : List AbstractNode :=
  w.parses.filterMap ExportedTree.toAbstractNode?

end SurfaceWitness

namespace WitnessBundle

/-- Successfully recovered abstract trees from all witnesses in the bundle. -/
def recoveredParses (b : WitnessBundle) : List (String × String × String × List AbstractNode) :=
  b.witnesses.map fun w => (w.label, w.language, w.surface, w.recoveredParses)

end WitnessBundle

end Mettapedia.Languages.GF.PGFWitnessIR
