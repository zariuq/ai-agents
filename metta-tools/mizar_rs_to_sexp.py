#!/usr/bin/env python3
"""
Convert mizar-rs JSON output to S-expressions for MeTTa/MORK.
This handles the actual JSON structure produced by mizar-rs --json-parse-out
"""

import json
import sys
from typing import Any, List, Union

def escape_string(s: str) -> str:
    """Escape special characters for S-expression strings"""
    if not s:
        return '""'
    # Escape backslashes and quotes
    s = s.replace('\\', '\\\\').replace('"', '\\"')
    return f'"{s}"'

def pos_to_sexp(pos: List[int]) -> str:
    """Convert position [line, col] to S-expression"""
    if pos:
        return f"(pos {pos[0]} {pos[1]})"
    return "nil"

def term_to_sexp(term: dict) -> str:
    """Convert a term to S-expression"""
    if not term:
        return "nil"

    # Handle different term types
    if "Var" in term:
        var = term["Var"]
        return f'(var {escape_string(var.get("spelling", ""))})'

    elif "Const" in term:
        const = term["Const"]
        return f'(const {const.get("id", 0)})'

    elif "It" in term:
        return "(it)"

    elif "Num" in term:
        return f'(num {term["Num"]})'

    elif "Func" in term:
        func = term["Func"]
        args = " ".join(term_to_sexp(arg) for arg in func.get("args", []))
        return f'(func {func.get("sym", 0)} {escape_string(func.get("spelling", ""))} {args})'

    elif "Bracket" in term:
        bracket = term["Bracket"]
        args = " ".join(term_to_sexp(arg) for arg in bracket.get("args", []))
        return f'(bracket {escape_string(bracket.get("lspelling", ""))} {escape_string(bracket.get("rspelling", ""))} {args})'

    elif "Aggregate" in term:
        agg = term["Aggregate"]
        args = " ".join(term_to_sexp(arg) for arg in agg.get("args", []))
        return f'(aggregate {args})'

    elif "PrivFunc" in term:
        pf = term["PrivFunc"]
        args = " ".join(term_to_sexp(arg) for arg in pf.get("args", []))
        return f'(priv-func {pf.get("id", 0)} {args})'

    # Handle raw dict with spelling (common in Bracket args)
    elif "spelling" in term and not "args" in term:
        return f'(var {escape_string(term.get("spelling", ""))})'

    # Handle patterns (predicates/functions used as patterns in definitions)
    elif "sym" in term and "spelling" in term and "args" in term:
        args = " ".join(term_to_sexp(arg) for arg in term.get("args", []))
        left = term.get("left", 0)
        if left > 0:  # Infix operator
            return f'(pattern-infix {term.get("sym", 0)} {escape_string(term.get("spelling", ""))} {left} ({args}))'
        else:
            return f'(pattern {term.get("sym", 0)} {escape_string(term.get("spelling", ""))} ({args}))'

    else:
        # Unknown term type - return raw dict as string
        return f'(unknown-term {str(term)})'

def type_to_sexp(ty: dict) -> str:
    """Convert a type to S-expression"""
    if not ty:
        return "nil"

    if "Mode" in ty:
        mode = ty["Mode"]
        return f'(mode {mode.get("sym", 0)} {escape_string(mode.get("spelling", ""))})'

    elif "Struct" in ty:
        struct = ty["Struct"]
        args = " ".join(term_to_sexp(arg) for arg in struct.get("args", []))
        return f'(struct {struct.get("sym", 0)} {args})'

    elif "Cluster" in ty:
        cluster = ty["Cluster"]
        attrs = " ".join(attr_to_sexp(attr) for attr in cluster.get("attrs", []))
        base = type_to_sexp(cluster.get("ty", {}))
        return f'(cluster ({attrs}) {base})'

    else:
        return f'(unknown-type {str(ty)})'

def attr_to_sexp(attr: dict) -> str:
    """Convert an attribute to S-expression"""
    if not attr:
        return "nil"

    pos = attr.get("positive", True)
    sym = attr.get("sym", 0)
    spelling = escape_string(attr.get("spelling", ""))
    args = " ".join(term_to_sexp(arg) for arg in attr.get("args", []))

    if args:
        return f'(attr {pos} {sym} {spelling} ({args}))'
    else:
        return f'(attr {pos} {sym} {spelling})'

def formula_to_sexp(formula: dict) -> str:
    """Convert a formula to S-expression"""
    if not formula:
        return "nil"

    # Check what's inside the formula dict
    if "f" in formula:
        return formula_node_to_sexp(formula["f"])
    else:
        return formula_node_to_sexp(formula)

def formula_node_to_sexp(f: dict) -> str:
    """Convert a formula node to S-expression"""
    if not f:
        return "nil"

    if "Neg" in f:
        inner = formula_node_to_sexp(f["Neg"])
        return f'(not {inner})'

    elif "Not" in f:  # Alternative negation format
        inner = formula_to_sexp(f["Not"])
        return f'(not {inner})'

    elif "Binop" in f:
        binop = f["Binop"]
        kind = binop.get("kind", "").lower()
        f1 = formula_node_to_sexp(binop.get("f1", {}))
        f2 = formula_node_to_sexp(binop.get("f2", {}))
        return f'({kind} {f1} {f2})'

    elif "Binder" in f:
        binder = f["Binder"]
        kind = binder.get("kind", "").lower()
        vars_list = []
        for var_group in binder.get("vars", []):
            var_names = " ".join(escape_string(v.get("spelling", "")) for v in var_group.get("vars", []))
            var_type = type_to_sexp(var_group.get("ty", {}))
            vars_list.append(f'({var_names} {var_type})')
        vars = " ".join(vars_list)
        scope = formula_node_to_sexp(binder.get("scope", {}))
        return f'({kind} ({vars}) {scope})'

    elif "Pred" in f:
        pred = f["Pred"]
        pos = "+" if pred.get("positive", True) else "-"
        sym = pred.get("sym", 0)
        spelling = escape_string(pred.get("spelling", ""))
        args = " ".join(term_to_sexp(arg) for arg in pred.get("args", []))
        return f'(pred {pos} {sym} {spelling} ({args}))'

    elif "Attr" in f:
        attr = f["Attr"]
        pos = "+" if attr.get("positive", True) else "-"
        sym = attr.get("sym", 0)
        spelling = escape_string(attr.get("spelling", ""))
        term = term_to_sexp(attr.get("term", {}))
        args = " ".join(term_to_sexp(arg) for arg in attr.get("args", []))
        if args:
            return f'(attr {pos} {sym} {spelling} {term} ({args}))'
        else:
            return f'(attr {pos} {sym} {spelling} {term})'

    elif "Is" in f:
        is_node = f["Is"]
        pos = "+" if is_node.get("positive", True) else "-"
        term = term_to_sexp(is_node.get("term", {}))
        ty = type_to_sexp(is_node.get("ty", {}))
        return f'(is {pos} {term} {ty})'

    elif "True" in f:
        return "true"

    elif "False" in f:
        return "false"

    else:
        return f'(unknown-formula {str(f)})'

def justification_to_sexp(just: dict) -> str:
    """Convert justification to S-expression"""
    if not just:
        return "nil"

    if "Inference" in just:
        inf = just["Inference"]
        kind = inf.get("kind", {})
        refs = " ".join(ref_to_sexp(ref) for ref in inf.get("refs", []))

        if "By" in kind:
            return f'(by {refs})'
        elif "From" in kind:
            scheme = ref_to_sexp(kind["From"].get("scheme", {}))
            return f'(from {scheme} {refs})'
        else:
            return f'(inference {refs})'

    elif "Proof" in just:
        # Full proof - would need to expand this
        return "(proof ...)"

    else:
        return "nil"

def ref_to_sexp(ref: dict) -> str:
    """Convert reference to S-expression"""
    if not ref:
        return "nil"

    kind = ref.get("kind", {})
    if isinstance(kind, dict):
        art = kind.get("art", 0)
        spelling = escape_string(kind.get("spelling", ""))
        refs = " ".join(inner_ref_to_sexp(r) for r in kind.get("refs", []))
        return f'(ref {art} {spelling} ({refs}))'
    else:
        return "nil"

def inner_ref_to_sexp(ref: dict) -> str:
    """Convert inner reference to S-expression"""
    if "Thm" in ref:
        return f'(thm {ref["Thm"].get("id", 0)})'
    elif "Def" in ref:
        return f'(def {ref["Def"].get("id", 0)})'
    elif "Sch" in ref:
        return f'(sch {ref["Sch"].get("id", 0)})'
    else:
        return "nil"

def item_to_sexp(item: dict) -> str:
    """Convert a body item to S-expression"""
    if not item:
        return "nil"

    pos = pos_to_sexp(item.get("pos", []))
    kind = item.get("kind", {})

    if "Theorem" in kind:
        thm = kind["Theorem"]
        prop = formula_to_sexp(thm.get("prop", {}))
        just = justification_to_sexp(thm.get("just", {}))
        return f'(theorem {pos} {prop} {just})'

    elif "Definition" in kind:
        defn = kind["Definition"]
        # Handle different definition kinds
        kind_inner = defn.get("kind", {})
        if "Func" in kind_inner:
            func = kind_inner["Func"]
            pat = term_to_sexp(func.get("pat", {}))
            spec = type_to_sexp(func.get("spec", {}))
            def_body = defn_body_to_sexp(func.get("def", {}))
            return f'(def-func {pos} {pat} {spec} {def_body})'
        elif "Pred" in kind_inner:
            pred = kind_inner["Pred"]
            pat = term_to_sexp(pred.get("pat", {}))
            def_body = defn_body_to_sexp(pred.get("def", {}))
            return f'(def-pred {pos} {pat} {def_body})'
        elif "Mode" in kind_inner:
            mode = kind_inner["Mode"]
            pat = term_to_sexp(mode.get("pat", {}))
            def_body = defn_body_to_sexp(mode.get("def", {}))
            return f'(def-mode {pos} {pat} {def_body})'
        elif "Attr" in kind_inner:
            attr = kind_inner["Attr"]
            pat = term_to_sexp(attr.get("pat", {}))
            def_body = defn_body_to_sexp(attr.get("def", {}))
            return f'(def-attr {pos} {pat} {def_body})'
        else:
            return f'(definition {pos} ...)'

    elif "Block" in kind:
        block = kind["Block"]
        block_kind = block.get("kind", "")
        items = " ".join(item_to_sexp(i) for i in block.get("items", []))
        return f'(block {block_kind} ({items}))'

    elif "Reservation" in kind:
        res = kind["Reservation"]
        parts = []
        for r in res:
            var_names = " ".join(escape_string(v.get("spelling", "")) for v in r.get("vars", []))
            ty = type_to_sexp(r.get("ty", {}))
            parts.append(f'({var_names} {ty})')
        return f'(reserve {" ".join(parts)})'

    elif "SchemeHead" in kind:
        return "(scheme ...)"

    elif "Let" in kind:
        let = kind["Let"]
        vars_list = []
        for var_group in let.get("vars", []):
            var_names = " ".join(escape_string(v.get("spelling", "")) for v in var_group.get("vars", []))
            var_type = type_to_sexp(var_group.get("ty", {}))
            vars_list.append(f'({var_names} {var_type})')
        vars = " ".join(vars_list)
        return f'(let {vars})'

    else:
        return f'(item {str(kind)[:50]}...)'

def defn_body_to_sexp(defn: dict) -> str:
    """Convert definition body to S-expression"""
    if not defn:
        return "nil"

    kind = defn.get("kind", {})
    if "Formula" in kind:
        f = formula_to_sexp(kind["Formula"].get("otherwise", {}))
        return f'(means {f})'
    elif "Simple" in kind:
        t = term_to_sexp(kind["Simple"])
        return f'(equals {t})'
    else:
        return "nil"

def convert_mizar_json_to_sexp(json_file: str, output_file: str = None):
    """Main conversion function"""

    with open(json_file, 'r') as f:
        data = json.load(f)

    lines = []

    # Header
    lines.append(f';; Mizar article converted from {json_file}')
    lines.append(f';; Version: {data.get("version", 0)}')
    lines.append('')

    # Vocabularies
    if data.get("vocabularies"):
        lines.append(';; Vocabularies')
        for vocab in data["vocabularies"]:
            art = escape_string(vocab.get("art", ""))
            pos = pos_to_sexp(vocab.get("pos", []))
            lines.append(f'(vocabulary {art} {pos})')
        lines.append('')

    # Requirements
    if data.get("requirements"):
        lines.append(';; Requirements')
        for req in data["requirements"]:
            art = escape_string(req.get("art", ""))
            pos = pos_to_sexp(req.get("pos", []))
            lines.append(f'(requirement {art} {pos})')
        lines.append('')

    # Main body
    lines.append(';; Article body')
    for item in data.get("body", []):
        sexp = item_to_sexp(item)
        lines.append(sexp)
        lines.append('')

    output = '\n'.join(lines)

    if output_file:
        with open(output_file, 'w') as f:
            f.write(output)
        print(f"Converted {json_file} -> {output_file}")
    else:
        print(output)

def main():
    if len(sys.argv) < 2:
        print("Usage: mizar_rs_to_sexp.py <input.json> [output.sexp]")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None

    convert_mizar_json_to_sexp(input_file, output_file)

if __name__ == "__main__":
    main()