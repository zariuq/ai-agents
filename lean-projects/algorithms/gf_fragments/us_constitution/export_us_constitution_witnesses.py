#!/usr/bin/env python3
"""Export US Constitution main-text GF witnesses into Lean.

This is the honest GF lane for the Constitution experiment:

* source clauses are exact fragments from the original main text;
* ParseEng/PGF is the parser when available;
* parse trees containing PGF meta holes (`?`) are rejected as not grounded;
* the generated Lean signature contains only functions actually used by
  accepted parse witnesses;
* downstream Lean checks the raw trees again with GFCore.check.
"""

from __future__ import annotations

import hashlib
import json
import os
import signal
import sys
import time
from dataclasses import dataclass
from pathlib import Path

GF_LD = "/home/zar/.local/gf-extract/usr/lib"
PGF_PY_EGG = Path("/home/zar/.local/gf-extract/usr/local/lib/python3.12/dist-packages/pgf-1.1-py3.12-linux-x86_64.egg")

ROOT = Path("/home/zar/claude")
PGF_PATH = ROOT / "gf-wordnet/build/ParseEng.pgf"
OUT_JSON = ROOT / "lean-projects/algorithms/gf_fragments/us_constitution/generated/us_constitution_parse_witnesses.json"
CORRECTIONS_PATH = ROOT / "lean-projects/algorithms/gf_fragments/us_constitution/grammar_corrections.json"
OUT_SIG = ROOT / "lean-projects/algorithms/Algorithms/GF/Generated/USConstitutionMainSig.lean"
OUT_WITNESSES = ROOT / "lean-projects/mettapedia/Mettapedia/Languages/GF/USConstitution/Generated/Witnesses.lean"
OUT_CONTEXT_COMPLETIONS = ROOT / "lean-projects/mettapedia/Mettapedia/Languages/GF/USConstitution/Generated/ContextCompletions.lean"

ARCHIVES_URL = "https://www.archives.gov/founding-docs/constitution-transcript"
CONGRESS_URL = "https://constitution.congress.gov/constitution/"
PARSE_TIMEOUT_SECONDS = 20


class ParseTimeout(Exception):
    pass


def raise_parse_timeout(signum, frame) -> None:
    raise ParseTimeout()


@dataclass(frozen=True)
class Clause:
    ident: str
    anchor: str
    source_text: str
    parser_input: str
    note: str


CLAUSES = [
    Clause("preambleEstablishJustice", "Preamble", "establish Justice", "establish Justice", "Preamble purpose fragment."),
    Clause(
        "articleISection1Vesting",
        "Article I, Section 1",
        "All legislative Powers herein granted shall be vested in a Congress of the United States",
        "All legislative Powers herein granted shall be vested in a Congress of the United States",
        "Legislative vesting fragment.",
    ),
    Clause(
        "articleISection2HouseComposition",
        "Article I, Section 2",
        "The House of Representatives shall be composed of Members chosen every second Year by the People of the several States",
        "The House of Representatives shall be composed of Members chosen every second Year by the People of the several States",
        "House composition and election fragment.",
    ),
    Clause(
        "articleISection2RepresentativeAge",
        "Article I, Section 2",
        "No Person shall be a Representative who shall not have attained to the Age of twenty five Years",
        "No Person shall be a Representative who shall not have attained to the Age of twenty five Years",
        "Representative age qualification fragment.",
    ),
    Clause(
        "articleISection3SenateImpeachments",
        "Article I, Section 3",
        "The Senate shall have the sole Power to try all Impeachments",
        "The Senate shall have the sole Power to try all Impeachments",
        "Senate impeachment-trial power fragment.",
    ),
    Clause(
        "articleISection5Rules",
        "Article I, Section 5",
        "Each House may determine the Rules of its Proceedings",
        "Each House may determine the Rules of its Proceedings",
        "Internal chamber rules fragment.",
    ),
    Clause(
        "articleISection7EveryBillPresented",
        "Article I, Section 7",
        "Every Bill shall be presented to the President of the United States",
        "Every Bill shall be presented to the President of the United States",
        "Presentment fragment.",
    ),
    Clause(
        "articleISection7PresidentSigns",
        "Article I, Section 7",
        "he shall sign it",
        "he shall sign it",
        "Presidential signature fragment.",
    ),
    Clause(
        "articleISection7BecomesLaw",
        "Article I, Section 7",
        "it shall be a Law",
        "it shall be a Law",
        "Bill-becomes-law fragment.",
    ),
    Clause("articleISection8DeclareWar", "Article I, Section 8", "To declare War", "To declare War", "Enumerated war power fragment."),
    Clause(
        "articleISection9Habeas",
        "Article I, Section 9",
        "The Privilege of the Writ of Habeas Corpus shall not be suspended",
        "The Privilege of the Writ of Habeas Corpus shall not be suspended",
        "Habeas suspension fragment.",
    ),
    Clause(
        "articleISection9NoTitleOfNobility",
        "Article I, Section 9",
        "No Title of Nobility shall be granted by the United States",
        "No Title of Nobility shall be granted by the United States",
        "Federal title-of-nobility prohibition fragment.",
    ),
    Clause(
        "articleIISection1ExecutiveVesting",
        "Article II, Section 1",
        "The executive Power shall be vested in a President of the United States of America",
        "The executive Power shall be vested in a President of the United States of America",
        "Executive vesting fragment.",
    ),
    Clause(
        "articleIISection1PresidentAge",
        "Article II, Section 1",
        "the Age of thirty five Years",
        "the Age of thirty five Years",
        "Presidential age-qualification fragment.",
    ),
    Clause(
        "articleIISection2CommanderInChief",
        "Article II, Section 2",
        "The President shall be Commander in Chief of the Army and Navy of the United States",
        "The President shall be Commander in Chief of the Army and Navy of the United States",
        "Commander-in-chief fragment.",
    ),
    Clause(
        "articleIIISection3Treason",
        "Article III, Section 3",
        "Treason against the United States shall consist only in levying War against them",
        "Treason against the United States shall consist only in levying War against them",
        "Treason definition fragment.",
    ),
    Clause(
        "articleIVSection1FullFaithCredit",
        "Article IV, Section 1",
        "Full Faith and Credit shall be given in each State to the public Acts Records and judicial Proceedings of every other State",
        "Full Faith and Credit shall be given in each State to the public Acts Records and judicial Proceedings of every other State",
        "Full faith and credit fragment.",
    ),
    Clause(
        "articleVProposeAmendments",
        "Article V",
        "shall propose Amendments to this Constitution",
        "shall propose Amendments to this Constitution",
        "Article V proposal fragment.",
    ),
    Clause(
        "articleVISupremacy",
        "Article VI",
        "This Constitution shall be the supreme Law of the Land",
        "This Constitution shall be the supreme Law of the Land",
        "Supremacy clause fragment.",
    ),
    Clause(
        "articleVINoReligiousTest",
        "Article VI",
        "no religious Test shall ever be required as a Qualification to any Office or public Trust under the United States",
        "no religious Test shall ever be required as a Qualification to any Office or public Trust under the United States",
        "No religious test fragment.",
    ),
    Clause(
        "articleVIIRatification",
        "Article VII",
        "The Ratification of the Conventions of nine States shall be sufficient for the Establishment of this Constitution",
        "The Ratification of the Conventions of nine States shall be sufficient for the Establishment of this Constitution",
        "Ratification threshold fragment.",
    ),
]


def ensure_runtime_libs() -> None:
    cur = os.environ.get("LD_LIBRARY_PATH", "")
    parts = [x for x in cur.split(":") if x]
    if GF_LD in parts:
        return
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = ":".join([GF_LD] + parts)
    os.execvpe(sys.executable, [sys.executable, __file__, *sys.argv[1:]], env)


def lean_str(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def has_meta_hole(tree: dict) -> bool:
    return tree["fun"] is None or tree["fun"] == "?" or any(has_meta_hole(arg) for arg in tree["args"])


def export_expr(expr) -> dict:
    fun, args = expr.unpack()
    return {"fun": fun, "args": [export_expr(arg) for arg in args]}


def collect_functions(tree: dict, out: set[str]) -> None:
    out.add(tree["fun"])
    for arg in tree["args"]:
        collect_functions(arg, out)


def linearization_info(concr, pgf_obj, expr, tree: dict) -> dict:
    linearization = concr.linearize(expr)
    bracketed = " ".join(str(b) for b in concr.bracketedLinearize(expr))
    return {
        "linearization": linearization,
        "bracketedLinearization": bracketed,
    }


def parse_accepted(concr, pgf_obj, parser_input: str) -> tuple[int, list[dict], list[dict], str | None]:
    raw_count = 0
    accepted: list[dict] = []
    accepted_infos: list[dict] = []
    error: str | None = None
    started_at = time.monotonic()
    old_handler = signal.signal(signal.SIGALRM, raise_parse_timeout)
    signal.alarm(PARSE_TIMEOUT_SECONDS)
    try:
        for prob, expr in concr.parse(parser_input, cat=pgf_obj.startCat):
            raw_count += 1
            tree = export_expr(expr)
            if not has_meta_hole(tree):
                accepted.append(tree)
                accepted_infos.append(linearization_info(concr, pgf_obj, expr, tree))
            if raw_count >= 3 or accepted:
                break
    except ParseTimeout:
        error = f"parse timed out after {PARSE_TIMEOUT_SECONDS}s"
    except Exception as exc:
        error = str(exc)
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, signal.SIG_IGN)
        signal.signal(signal.SIGALRM, old_handler)
    elapsed = time.monotonic() - started_at
    if error is None and not accepted and PARSE_TIMEOUT_SECONDS <= elapsed:
        error = f"parse timed out after {PARSE_TIMEOUT_SECONDS}s"
    if error is None and not accepted:
        error = "no accepted parse without PGF meta holes"
    return raw_count, accepted, accepted_infos, error


def parse_type(type_text: str) -> tuple[list[str], str]:
    parts = [p.strip() for p in type_text.split("->")]
    if not parts or not parts[-1]:
        raise ValueError(f"cannot parse GF type: {type_text!r}")
    return parts[:-1], parts[-1]


def render_tree(tree: dict, indent: str = "") -> str:
    if not tree["args"]:
        return f'.node {lean_str(tree["fun"])} []'
    child_indent = indent + "  "
    children = ",\n".join(child_indent + render_tree(arg, child_indent) for arg in tree["args"])
    return f'.node {lean_str(tree["fun"])} [\n{children}\n{indent}]'


def render_clause_constructor(c: Clause) -> str:
    return f"  | {c.ident}"


def render_clause_match(fn: str, pairs: list[tuple[str, str]]) -> str:
    lines = [f"def {fn} : ClauseId → String"]
    for ident, value in pairs:
        lines.append(f"  | .{ident} => {lean_str(value)}")
    return "\n".join(lines)


def render_clause_string_list_match(fn: str, pairs: list[tuple[str, list[str]]]) -> str:
    lines = [f"def {fn} : ClauseId → List String"]
    for ident, values in pairs:
        rendered = "[" + ", ".join(lean_str(v) for v in values) + "]"
        lines.append(f"  | .{ident} => {rendered}")
    return "\n".join(lines)


def render_correction_constructor(entry: dict) -> str:
    return f"  | {entry['id']}"


def render_correction_match(fn: str, result_type: str, pairs: list[tuple[str, str]]) -> str:
    lines = [f"def {fn} : CorrectionId → {result_type}"]
    for ident, value in pairs:
        lines.append(f"  | .{ident} => {value}")
    return "\n".join(lines)


def render_correction_string_list_match(fn: str, pairs: list[tuple[str, list[str]]]) -> str:
    lines = [f"def {fn} : CorrectionId → List String"]
    for ident, values in pairs:
        rendered = "[" + ", ".join(lean_str(v) for v in values) + "]"
        lines.append(f"  | .{ident} => {rendered}")
    return "\n".join(lines)


def render_sig(grammar_name: str, source_hash: str, fun_types: dict[str, tuple[list[str], str]]) -> str:
    decls: list[str] = []
    entries: list[str] = []
    for idx, (fun, (args, result)) in enumerate(sorted(fun_types.items())):
        def_name = f"fd{idx}"
        arg_array = "#[" + ", ".join(lean_str(a) for a in args) + "]"
        decls.append(
            f"private def {def_name} : FunDecl :=\n"
            f"  {{ name := {lean_str(fun)}, argCats := {arg_array}, resultCat := {lean_str(result)}, status := .primitive }}"
        )
        entries.append(f"    ({lean_str(fun)}, {def_name}),")
    return f"""-- AUTO-GENERATED from ParseEng PGF witnesses. Do not edit.
-- Grammar: {grammar_name}
-- Source hash: {source_hash}
-- Functions: {len(fun_types)}

import GFCore.Syntax
import Std.Data.HashMap

namespace Algorithms.GF.Generated.USConstitutionMainSig

open GFCore

{chr(10).join(decls)}

/-- The list of function declarations (kernel-reducible). -/
def funsList : List (String × FunDecl) :=
  [
{chr(10).join(entries)}
  ]

def sig : GrammarSig where
  grammar := {lean_str(grammar_name)}
  startCats := #["Phr"]
  sourceHash := {lean_str(source_hash)}
  funs := Std.HashMap.ofList funsList

end Algorithms.GF.Generated.USConstitutionMainSig
"""


def render_witnesses(source_hash: str, bundle: dict) -> str:
    clauses = [Clause(**c) for c in bundle["clauses"]]
    constructor_lines = "\n".join(render_clause_constructor(c) for c in clauses)
    ids = ", ".join(f".{c.ident}" for c in clauses)
    text_match = render_clause_match("clauseText", [(c.ident, c.source_text) for c in clauses])
    input_match = render_clause_match("parserInput", [(c.ident, c.parser_input) for c in clauses])
    anchor_match = render_clause_match("clauseAnchor", [(c.ident, c.anchor) for c in clauses])
    note_match = render_clause_match("clauseNote", [(c.ident, c.note) for c in clauses])
    defs: list[str] = []
    parses_match: list[str] = ["def clauseParses : ClauseId → List ExportedTree"]
    raw_count_match: list[str] = ["def rawParseCount : ClauseId → Nat"]
    accepted_count_match: list[str] = ["def acceptedParseCount : ClauseId → Nat"]
    error_match: list[str] = ["def parseError : ClauseId → Option String"]
    linearization_pairs: list[tuple[str, list[str]]] = []
    bracketed_pairs: list[tuple[str, list[str]]] = []
    for entry in bundle["witnesses"]:
        ident = entry["id"]
        parse_names: list[str] = []
        for idx, tree in enumerate(entry["acceptedParses"], start=1):
            name = f"{ident}Parse{idx}"
            parse_names.append(name)
            defs.append(f"def {name} : ExportedTree :=\n  {render_tree(tree, '  ')}")
        parses_match.append(f"  | .{ident} => [{', '.join(parse_names)}]")
        raw_count_match.append(f"  | .{ident} => {entry['rawParseCount']}")
        accepted_count_match.append(f"  | .{ident} => {len(entry['acceptedParses'])}")
        infos = entry.get("acceptedInfos", [])
        linearization_pairs.append((ident, [info["linearization"] for info in infos]))
        bracketed_pairs.append((ident, [info["bracketedLinearization"] for info in infos]))
        if entry["error"]:
            error_match.append(f"  | .{ident} => some {lean_str(entry['error'])}")
        else:
            error_match.append(f"  | .{ident} => none")
    used = ", ".join(lean_str(f) for f in bundle["usedFunctions"])
    return f"""-- AUTO-GENERATED from ParseEng PGF witnesses. Do not edit.

import Mettapedia.Languages.GF.PGFWitnessIR

namespace Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

open Mettapedia.Languages.GF.PGFWitnessIR

inductive ClauseId where
{constructor_lines}
  deriving Repr, DecidableEq

def sourceHash : String := {lean_str(source_hash)}
def grammarName : String := {lean_str(bundle["grammar"])}
def archivesSourceUrl : String := {lean_str(ARCHIVES_URL)}
def congressSourceUrl : String := {lean_str(CONGRESS_URL)}

def allClauseIds : List ClauseId := [{ids}]

{text_match}

{input_match}

{anchor_match}

{note_match}

{chr(10).join(defs)}

{chr(10).join(parses_match)}

{chr(10).join(raw_count_match)}

{chr(10).join(accepted_count_match)}

{chr(10).join(error_match)}

{render_clause_string_list_match("clauseGFLinearizations", linearization_pairs)}

{render_clause_string_list_match("clauseGFBracketedLinearizations", bracketed_pairs)}

def usedFunctions : List String := [{used}]

end Mettapedia.Languages.GF.USConstitution.Generated.Witnesses
"""


def render_context_completions(source_hash: str, bundle: dict) -> str:
    clauses = [Clause(**c) for c in bundle["clauses"]]
    corrections = bundle["contextCompletions"]
    constructor_lines = "\n".join(render_correction_constructor(c) for c in corrections)
    ids = ", ".join(f".{c['id']}" for c in corrections)
    kinds = {
        "exact_subfragment": ".exactSubfragment",
        "context_completion": ".contextCompletion",
    }
    defs: list[str] = []
    parses_match: list[str] = ["def correctionParses : CorrectionId → List ExportedTree"]
    for entry in corrections:
        ident = entry["id"]
        parse_names: list[str] = []
        for idx, tree in enumerate(entry["acceptedParses"], start=1):
            name = f"{ident}Parse{idx}"
            parse_names.append(name)
            defs.append(f"def {name} : ExportedTree :=\n  {render_tree(tree, '  ')}")
        parses_match.append(f"  | .{ident} => [{', '.join(parse_names)}]")

    source_clause_match = render_correction_match(
        "sourceClause", "ClauseId",
        [(c["id"], f".{c['clauseId']}") for c in corrections],
    )
    kind_match = render_correction_match(
        "correctionKind", "CorrectionKind",
        [(c["id"], kinds[c["kind"]]) for c in corrections],
    )
    input_match = render_correction_match(
        "correctionParserInput", "String",
        [(c["id"], lean_str(c["parserInput"])) for c in corrections],
    )
    confidence_match = render_correction_match(
        "confidencePermille", "Nat",
        [(c["id"], str(c["confidencePermille"])) for c in corrections],
    )
    justification_match = render_correction_match(
        "correctionJustification", "String",
        [(c["id"], lean_str(c["justification"])) for c in corrections],
    )
    source_match = render_correction_match(
        "correctionSource", "String",
        [(c["id"], lean_str(c["source"])) for c in corrections],
    )
    raw_count_match = render_correction_match(
        "rawParseCount", "Nat",
        [(c["id"], str(c["rawParseCount"])) for c in corrections],
    )
    accepted_count_match = render_correction_match(
        "acceptedParseCount", "Nat",
        [(c["id"], str(len(c["acceptedParses"]))) for c in corrections],
    )
    linearization_match = render_correction_string_list_match(
        "correctionGFLinearizations",
        [(c["id"], [info["linearization"] for info in c.get("acceptedInfos", [])]) for c in corrections],
    )
    bracketed_match = render_correction_string_list_match(
        "correctionGFBracketedLinearizations",
        [(c["id"], [info["bracketedLinearization"] for info in c.get("acceptedInfos", [])]) for c in corrections],
    )

    corrections_by_clause: dict[str, list[str]] = {}
    for entry in corrections:
        corrections_by_clause.setdefault(entry["clauseId"], []).append(entry["id"])
    by_clause_lines = ["def correctionsForClause : ClauseId → List CorrectionId"]
    for clause in clauses:
        ids_for_clause = ", ".join(f".{ident}" for ident in corrections_by_clause.get(clause.ident, []))
        by_clause_lines.append(f"  | .{clause.ident} => [{ids_for_clause}]")

    return f"""-- AUTO-GENERATED from ParseEng PGF context-completion witnesses. Do not edit.

import Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

namespace Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions

open Mettapedia.Languages.GF.PGFWitnessIR
open Mettapedia.Languages.GF.USConstitution.Generated.Witnesses

inductive CorrectionKind where
  | exactSubfragment
  | contextCompletion
  deriving Repr, DecidableEq

inductive CorrectionId where
{constructor_lines}
  deriving Repr, DecidableEq

def sourceHash : String := {lean_str(source_hash)}
def correctionLogHash : String := {lean_str(bundle["correctionLogHash"])}
def allCorrectionIds : List CorrectionId := [{ids}]

{source_clause_match}

{kind_match}

{input_match}

{confidence_match}

{justification_match}

{source_match}

{chr(10).join(defs)}

{chr(10).join(parses_match)}

{raw_count_match}

{accepted_count_match}

{linearization_match}

{bracketed_match}

{chr(10).join(by_clause_lines)}

end Mettapedia.Languages.GF.USConstitution.Generated.ContextCompletions
"""


def main() -> None:
    ensure_runtime_libs()
    if not PGF_PATH.exists():
        raise SystemExit(f"missing {PGF_PATH}; build ParseEng.pgf before exporting")
    sys.path.insert(0, str(PGF_PY_EGG))
    import pgf  # type: ignore

    pgf_obj = pgf.readPGF(str(PGF_PATH))
    concr = pgf_obj.languages["ParseEng"]
    witnesses: list[dict] = []
    used_functions: set[str] = set()
    for clause in CLAUSES:
        raw_count, accepted, accepted_infos, error = parse_accepted(concr, pgf_obj, clause.parser_input)
        for tree in accepted:
            collect_functions(tree, used_functions)
        witnesses.append({
            "id": clause.ident,
            "anchor": clause.anchor,
            "source_text": clause.source_text,
            "parser_input": clause.parser_input,
            "note": clause.note,
            "rawParseCount": raw_count,
            "acceptedParses": accepted,
            "acceptedInfos": accepted_infos,
            "error": error,
        })

    correction_log_text = CORRECTIONS_PATH.read_text()
    correction_log_hash = hashlib.sha256(correction_log_text.encode("utf-8")).hexdigest()
    correction_log = json.loads(correction_log_text)
    context_completions: list[dict] = []
    kind_suffix = {
        "exact_subfragment": "ExactSubfragment",
        "context_completion": "ContextCompletion",
    }
    kind_counts: dict[tuple[str, str], int] = {}
    for entry in correction_log["corrections"]:
        clause_id = entry["clauseId"]
        for fix in entry["candidateFixes"]:
            if not fix.get("applyAsWitness", False):
                continue
            kind = fix["kind"]
            if kind not in kind_suffix:
                raise SystemExit(f"cannot apply unsupported correction kind {kind!r} for {clause_id}")
            key = (clause_id, kind)
            kind_counts[key] = kind_counts.get(key, 0) + 1
            ident = f"{clause_id}{kind_suffix[kind]}{kind_counts[key]}"
            raw_count, accepted, accepted_infos, error = parse_accepted(concr, pgf_obj, fix["parserInput"])
            if not accepted:
                raise SystemExit(f"applied correction {ident} failed to parse without holes: {error}")
            for tree in accepted:
                collect_functions(tree, used_functions)
            context_completions.append({
                "id": ident,
                "clauseId": clause_id,
                "kind": kind,
                "parserInput": fix["parserInput"],
                "confidencePermille": int(round(float(fix["confidence"]) * 1000)),
                "justification": fix["justification"],
                "source": fix["source"],
                "rawParseCount": raw_count,
                "acceptedParses": accepted,
                "acceptedInfos": accepted_infos,
                "error": error,
            })

    fun_types: dict[str, tuple[list[str], str]] = {}
    for fun in sorted(used_functions):
        args, result = parse_type(str(pgf_obj.functionType(fun)))
        fun_types[fun] = (args, result)

    source_blob = json.dumps({
        "clauses": [c.__dict__ for c in CLAUSES],
        "correctionLogSha256": correction_log_hash,
        "parseTimeoutSeconds": PARSE_TIMEOUT_SECONDS,
        "pgfSha256": hashlib.sha256(PGF_PATH.read_bytes()).hexdigest(),
    }, ensure_ascii=False, sort_keys=True)
    source_hash = hashlib.sha256(source_blob.encode("utf-8")).hexdigest()
    bundle = {
        "grammar": pgf_obj.abstractName,
        "sourceHash": source_hash,
        "pgfPath": str(PGF_PATH),
        "sourceUrls": [ARCHIVES_URL, CONGRESS_URL],
        "clauses": [c.__dict__ for c in CLAUSES],
        "witnesses": witnesses,
        "contextCompletions": context_completions,
        "correctionLogHash": correction_log_hash,
        "usedFunctions": sorted(used_functions),
    }
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(bundle, ensure_ascii=False, indent=2) + "\n")
    OUT_SIG.write_text(render_sig(pgf_obj.abstractName, source_hash, fun_types))
    OUT_WITNESSES.parent.mkdir(parents=True, exist_ok=True)
    OUT_WITNESSES.write_text(render_witnesses(source_hash, bundle))
    OUT_CONTEXT_COMPLETIONS.write_text(render_context_completions(source_hash, bundle))
    print(f"wrote {OUT_JSON}")
    print(f"wrote {OUT_SIG}")
    print(f"wrote {OUT_WITNESSES}")
    print(f"wrote {OUT_CONTEXT_COMPLETIONS}")
    print(
        f"clauses={len(CLAUSES)} accepted={sum(1 for w in witnesses if w['acceptedParses'])} "
        f"contextCompletions={len(context_completions)} functions={len(used_functions)}"
    )


if __name__ == "__main__":
    main()
