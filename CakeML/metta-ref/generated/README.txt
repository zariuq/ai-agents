Generated bridge artifacts
==========================

This directory is for CakeML artifacts emitted by HOL bridge scripts.

bridge_eval_match_fragment.sexp is emitted by
/home/zar/claude/CakeML/metta-ref/hol/metta_m1_cake_bridgeScript.sml from the
CakeML translator program state after bridge_eval_match_fragment is translated.
It is an auditable artifact, not a semantic source of truth. The corresponding
proof objects are the translator theorem, app spec, and CF wrapper theorems in
the HOL bridge theory.

The Makefile target check-generated-match-sexp consumes this artifact through
the CakeML compiler's s-expression input mode and emits an ignored assembly
file. That target is a harness check for artifact shape, not a replacement for
the HOL certificates.

The HOL bridge theory records the expected artifact names in
bridge_eval_match_fragment_artifact_manifest_checked and ties the manifest to
the semantic match-branch theorem in
bridge_eval_match_fragment_artifact_manifest_points_to_match_branch. The
manifest does not define semantics; it points back to the HOL certificate.
