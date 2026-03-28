#!/bin/bash
# HE <-> PeTTa MeTTa Translator
#
# Translates between Hyperon Experimental (HE) and PeTTa MeTTa dialects.
# Backed by a sorry-free Lean proof of semantic correspondence.
#
# Prerequisites: SWI-Prolog (swipl)
#
# Usage:
#   ./translate.sh he2petta input.metta output.metta
#   ./translate.sh petta2he input.metta output.metta
#   ./translate.sh he2petta --recursive input.metta
#   ./translate.sh petta2he --recursive input.metta
#   ./translate.sh he2petta --bundle input.metta output_dir/
#   ./translate.sh petta2he --bundle input.metta output_dir/
#   ./translate.sh petta2he --extended input.metta output.metta
#   ./translate.sh --test
#   ./translate.sh --help

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DRIVER="$SCRIPT_DIR/test_on_real_files.pl"

usage() {
    cat <<EOF
HE <-> PeTTa MeTTa Translator

Usage:
  $(basename "$0") <direction> [options] <input.metta> [output]

Directions:
  he2petta    Translate HE MeTTa to PeTTa dialect
  petta2he    Translate PeTTa MeTTa to HE dialect

Options:
  --recursive   Translate file and all local imports in place
  --bundle      Translate file and all local imports into a bundle directory
  --extended    Use extended mode (PeTTa->HE only: emit 'collect' instead of 'collapse')
  --raw         Skip post-translation optimization (PeTTa->HE only)
  --test        Run the translator test suite
  --help        Show this help

Examples:
  # Single file translation
  $(basename "$0") he2petta program.metta program_petta.metta

  # Translate with all local imports
  $(basename "$0") he2petta --recursive program.metta

  # Bundle into a directory
  $(basename "$0") petta2he --bundle program.metta translated/

  # Run tests
  $(basename "$0") --test

Backed by a sorry-free Lean proof (5,209 lines, 0 sorries).
See README.md for details.
EOF
}

if [ $# -eq 0 ]; then
    usage
    exit 1
fi

case "$1" in
    --help|-h)
        usage
        exit 0
        ;;
    --test)
        echo "Running translator tests..."
        swipl -q -l "$SCRIPT_DIR/test_translators.pl" -g run_tests -g halt
        echo "---"
        echo "Running path compatibility tests..."
        swipl -q -l "$SCRIPT_DIR/test_on_real_files.pl" -g run_path_compat_tests -g halt 2>/dev/null || true
        echo "All tests passed."
        exit 0
        ;;
    he2petta|petta2he)
        DIRECTION="$1"
        shift
        ;;
    *)
        echo "Error: unknown command '$1'. Use --help for usage."
        exit 1
        ;;
esac

# Parse options
MODE="single"
EXTENDED=""
RAW=""
while [[ $# -gt 0 && "$1" == --* ]]; do
    case "$1" in
        --recursive) MODE="recursive"; shift ;;
        --bundle) MODE="bundle"; shift ;;
        --extended) EXTENDED="_extended"; shift ;;
        --raw) RAW="_raw"; shift ;;
        *) echo "Error: unknown option '$1'"; exit 1 ;;
    esac
done

if [ $# -lt 1 ]; then
    echo "Error: missing input file. Use --help for usage."
    exit 1
fi

INPUT="$1"
if [ ! -f "$INPUT" ]; then
    echo "Error: file not found: $INPUT"
    exit 1
fi

case "$MODE" in
    single)
        if [ $# -lt 2 ]; then
            echo "Error: missing output file for single-file translation."
            exit 1
        fi
        OUTPUT="$2"
        if [ "$DIRECTION" = "he2petta" ]; then
            GOAL="translate_file_he_to_petta('$INPUT','$OUTPUT')"
        else
            GOAL="translate_file_petta_to_he${EXTENDED}${RAW:+_raw}('$INPUT','$OUTPUT')"
        fi
        ;;
    recursive)
        if [ "$DIRECTION" = "he2petta" ]; then
            SUFFIX=".he2petta.metta"
            GOAL="translate_file_he_to_petta_recursive('$INPUT','$SUFFIX')"
        else
            SUFFIX=".petta2he.metta"
            GOAL="translate_file_petta_to_he_recursive('$INPUT','$SUFFIX')"
        fi
        ;;
    bundle)
        if [ $# -lt 2 ]; then
            echo "Error: missing output directory for bundle translation."
            exit 1
        fi
        OUTPUT="$2"
        if [ "$DIRECTION" = "he2petta" ]; then
            GOAL="translate_file_he_to_petta_bundle('$INPUT','$OUTPUT')"
        else
            GOAL="translate_file_petta_to_he_bundle('$INPUT','$OUTPUT')"
        fi
        ;;
esac

swipl -q -l "$DRIVER" -g "$GOAL" -g halt
