import Mettapedia.OSLF.Framework.PyashGF

open Mettapedia.OSLF.Framework.PyashGF

private def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportPyashGFCanary.lean"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportPyashGFCanary.lean <case_out>"
    ]

/--
Emit focused GF-connected Pyash canary cases.

- No args: print canary case bundle to stdout.
- 1 arg: write canary case bundle to a file.
-/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.println renderPyashGFCanaryBundle
      pure 0
  | [caseOut] =>
      IO.FS.writeFile caseOut (renderPyashGFCanaryBundle ++ "\n")
      pure 0
  | _ =>
      IO.eprintln usage
      pure 1
