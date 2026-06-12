#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cake="${CAKE:-/home/zar/claude/CakeML/cake-x64-64/cake}"
src="$root/generated/bridge_eval_match_fragment.sexp"
out="$root/generated/bridge_eval_match_fragment.S"

test -s "$src"

# astToSexprLib emits the legacy unknown_loc token; the current CakeML
# s-expression parser expects the concrete unknown-location pair.
sed 's/unknown_loc/(unk unk)/g' "$src" |
  "$cake" --sexp=true --skip_type_inference=true > "$out"

test -s "$out"
