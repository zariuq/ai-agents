import Mettapedia.Languages.MeTTa.HE.RewriteIRV2

/-!
# HE Rewrite IR v2 Draft Export Tool

Thin CLI wrapper for the sidecar draft exporter/checker.

Usage:
  lake env lean --run Mettapedia/OSLF/Tools/ExportMeTTaHERewriteIRV2.lean export
  lake env lean --run Mettapedia/OSLF/Tools/ExportMeTTaHERewriteIRV2.lean export <out-dir>
  lake env lean --run Mettapedia/OSLF/Tools/ExportMeTTaHERewriteIRV2.lean check
  lake env lean --run Mettapedia/OSLF/Tools/ExportMeTTaHERewriteIRV2.lean check <out-dir>

This only touches the `he.rewrite_ir_v2_draft.*` sidecar files.
It does not mutate the live `he.rewrite_ir.*` contract.
-/

open Mettapedia.Languages.MeTTa.HE.RewriteIRV2

def main (args : List String) : IO UInt32 :=
  runCli args
