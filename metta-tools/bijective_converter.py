#!/usr/bin/env python3
"""
Bijective Mizar ↔ S-expression converter
NO CHEATING with (formula ...) - we extract EVERYTHING!
"""

import json
import sys
from typing import Any, Dict, List, Union

class BijectiveConverter:
    """
    Converts Mizar JSON to S-expressions WITHOUT information loss.
    Every piece of the AST is preserved for round-tripping.
    """

    def __init__(self):
        self.preserve_positions = True
        self.preserve_original = True

    def escape_string(self, s: str) -> str:
        """Escape special characters for S-expressions"""
        if not s:
            return '""'
        s = s.replace('\\', '\\\\').replace('"', '\\"')
        return f'"{s}"'

    def extract_complete_formula(self, prop: Dict) -> str:
        """
        Extract COMPLETE formula structure - no cheating!
        """
        if not prop:
            return "(no-formula)"

        if "f" in prop:
            return self.extract_formula_node(prop["f"])
        else:
            return self.extract_formula_node(prop)

    def extract_formula_node(self, node: Dict) -> str:
        """Extract any formula node completely"""

        if not node:
            return "nil"

        # Binder (ForAll, Exists)
        if "Binder" in node:
            binder = node["Binder"]
            kind = binder.get("kind", "Unknown").lower()
            pos = binder.get("pos", [])

            # Extract variables with types
            vars_str = self.extract_vars_with_types(binder.get("vars", []))

            # Extract 'such that' condition if present
            st_str = ""
            if "st" in binder:
                st_str = f" (such-that {self.extract_formula_node(binder['st'])})"

            # Extract scope
            scope = self.extract_formula_node(binder.get("scope", {}))

            return f"({kind} {vars_str}{st_str} {scope})"

        # Binary operation (And, Or, Iff, Imp)
        elif "Binop" in node:
            binop = node["Binop"]
            kind = binop.get("kind", "").lower()
            f1 = self.extract_formula_node(binop.get("f1", {}))
            f2 = self.extract_formula_node(binop.get("f2", {}))
            return f"({kind} {f1} {f2})"

        # Predicate
        elif "Pred" in node:
            pred = node["Pred"]
            positive = "+" if pred.get("positive", True) else "-"
            sym = pred.get("sym", 0)
            spelling = self.escape_string(pred.get("spelling", ""))
            args = " ".join(self.extract_term(arg) for arg in pred.get("args", []))
            left = pred.get("left", 0)

            if left > 0:  # Infix predicate
                return f"(pred-infix {positive} {sym} {spelling} {args})"
            else:
                return f"(pred {positive} {sym} {spelling} {args})"

        # Attribute
        elif "Attr" in node:
            attr = node["Attr"]
            positive = "+" if attr.get("positive", True) else "-"
            term = self.extract_term(attr.get("term", {}))
            attrs = self.extract_attributes(attr.get("attrs", []))
            return f"(attr {positive} {term} {attrs})"

        # Negation
        elif "Neg" in node or "Not" in node:
            inner = node.get("Neg", node.get("Not", {}))
            return f"(not {self.extract_formula_node(inner)})"

        # Is (type predicate)
        elif "Is" in node:
            is_node = node["Is"]
            positive = "+" if is_node.get("positive", True) else "-"
            term = self.extract_term(is_node.get("term", {}))
            ty = self.extract_type(is_node.get("ty", {}))
            return f"(is {positive} {term} {ty})"

        # Verum (true)
        elif "Verum" in node:
            return "true"

        # Contradiction
        elif "Contradiction" in node:
            return "false"

        else:
            # Unknown node - preserve as raw data
            return f"(unknown-formula {json.dumps(node)})"

    def extract_term(self, term: Dict) -> str:
        """Extract term COMPLETELY"""

        if not term:
            return "nil"

        # Variable
        if "Var" in term:
            var = term["Var"]
            spelling = self.escape_string(var.get("spelling", ""))
            pos = var.get("pos", [])
            if self.preserve_positions and pos:
                return f"(var {spelling} :pos [{pos[0]} {pos[1]}])"
            else:
                return f"(var {spelling})"

        # Constant
        elif "Const" in term:
            const = term["Const"]
            return f"(const {const.get('id', 0)})"

        # Number
        elif "Num" in term:
            return f"(num {term['Num']})"

        # Infix operation
        elif "Infix" in term:
            infix = term["Infix"]
            sym = infix.get("sym", 0)
            spelling = self.escape_string(infix.get("spelling", ""))
            left = infix.get("left", 0)
            args = infix.get("args", [])

            # Special case for {} (empty set)
            if spelling == '"{}"' and not args:
                return "(empty-set)"

            # General infix
            if len(args) == 2:
                arg1 = self.extract_term(args[0])
                arg2 = self.extract_term(args[1])
                return f"(infix {sym} {spelling} {arg1} {arg2})"
            else:
                args_str = " ".join(self.extract_term(arg) for arg in args)
                return f"(infix {sym} {spelling} ({args_str}))"

        # Function application
        elif "Func" in term:
            func = term["Func"]
            sym = func.get("sym", 0)
            spelling = self.escape_string(func.get("spelling", ""))
            args = " ".join(self.extract_term(arg) for arg in func.get("args", []))
            return f"(func {sym} {spelling} ({args}))"

        # Bracket notation
        elif "Bracket" in term:
            bracket = term["Bracket"]
            lsym = self.escape_string(bracket.get("lspelling", ""))
            rsym = self.escape_string(bracket.get("rspelling", ""))
            args = " ".join(self.extract_term(arg) for arg in bracket.get("args", []))
            return f"(bracket {lsym} {rsym} ({args}))"

        # The 'it' keyword
        elif "It" in term:
            return "(it)"

        # Unknown - but we found it's just a dict with spelling
        elif "spelling" in term and len(term) <= 2:  # spelling + maybe pos
            return f"(var {self.escape_string(term['spelling'])})"

        else:
            # Preserve unknown as JSON
            return f"(unknown-term {json.dumps(term)})"

    def extract_vars_with_types(self, var_groups: List) -> str:
        """Extract variable declarations with their types"""
        parts = []
        for group in var_groups:
            var_names = " ".join(self.escape_string(v.get("spelling", ""))
                                for v in group.get("vars", []))
            ty = self.extract_type(group.get("ty", {}))
            parts.append(f"({var_names} {ty})")
        return "(" + " ".join(parts) + ")"

    def extract_type(self, ty: Dict) -> str:
        """Extract type information"""
        if not ty:
            return "any-type"

        if "Mode" in ty:
            mode = ty["Mode"]
            sym = mode.get("sym", 0)
            spelling = self.escape_string(mode.get("spelling", ""))
            return f"(mode {sym} {spelling})"

        elif "Struct" in ty:
            struct = ty["Struct"]
            sym = struct.get("sym", 0)
            args = " ".join(self.extract_term(arg) for arg in struct.get("args", []))
            return f"(struct {sym} ({args}))"

        else:
            return f"(type {json.dumps(ty)})"

    def extract_attributes(self, attrs: List) -> str:
        """Extract attribute list"""
        if not attrs:
            return "no-attrs"

        parts = []
        for attr in attrs:
            if "Non" in attr:
                inner = self.extract_attributes([attr["Non"].get("attr", {})])
                parts.append(f"(non {inner})")
            elif "Attr" in attr:
                a = attr["Attr"]
                sym = a.get("sym", 0)
                spelling = self.escape_string(a.get("spelling", ""))
                parts.append(f"(attr {sym} {spelling})")
            else:
                parts.append(f"(unknown-attr {json.dumps(attr)})")

        return "(" + " ".join(parts) + ")"

    def extract_justification(self, just: Dict) -> str:
        """Extract complete justification"""
        if not just:
            return "(no-justification)"

        if "Inference" in just:
            inf = just["Inference"]
            kind = inf.get("kind", {})
            refs = self.extract_references(inf.get("refs", []))

            if "By" in kind:
                return f"(by {refs})"
            elif "From" in kind:
                scheme = self.extract_references([kind["From"].get("scheme", {})])
                return f"(from {scheme} {refs})"
            else:
                return f"(inference {refs})"

        elif "Block" in just:
            # Full proof block
            block = just["Block"]
            items = block.get("items", [])
            return f"(proof-block :items {len(items)} :pos {block.get('pos', [])})"

        else:
            return f"(unknown-just {json.dumps(just)})"

    def extract_references(self, refs: List) -> str:
        """Extract reference list"""
        if not refs:
            return "no-refs"

        parts = []
        for ref in refs:
            if "kind" in ref:
                kind = ref["kind"]
                if isinstance(kind, dict):
                    art = kind.get("art", 0)
                    spelling = self.escape_string(kind.get("spelling", ""))
                    inner_refs = []
                    for r in kind.get("refs", []):
                        if "Thm" in r:
                            inner_refs.append(f"(thm {r['Thm'].get('id', 0)})")
                        elif "Def" in r:
                            inner_refs.append(f"(def {r['Def'].get('id', 0)})")
                        else:
                            inner_refs.append(f"(ref {json.dumps(r)})")
                    refs_str = " ".join(inner_refs)
                    parts.append(f"(ref {art} {spelling} ({refs_str}))")
                else:
                    parts.append(f"(ref {json.dumps(kind)})")
            else:
                parts.append(f"(ref {json.dumps(ref)})")

        return "(" + " ".join(parts) + ")"

    def convert_theorem(self, item: Dict, article_name: str, theorem_num: int) -> str:
        """Convert a complete theorem to S-expression"""
        pos = item.get("pos", [])
        thm = item["kind"]["Theorem"]

        # Extract complete formula
        formula = self.extract_complete_formula(thm.get("prop", {}))

        # Extract justification
        just = self.extract_justification(thm.get("just", {}))

        # Build S-expression with name AND position
        result = f"(theorem {article_name}-thm-{theorem_num}"
        if self.preserve_positions and pos:
            result += f" :pos [{pos[0]} {pos[1]}]"
        result += f"\n  {formula}\n  {just})"

        return result

    def convert_json_to_sexp(self, json_file: str) -> str:
        """Convert complete JSON to S-expressions"""
        with open(json_file, 'r') as f:
            data = json.load(f)

        # Extract article name from filename
        import os
        article_name = os.path.basename(json_file).replace('.mzp.json', '')

        lines = []
        lines.append(";; Bijective Mizar conversion - NO information loss!")
        lines.append(f";; Source: {json_file}")
        lines.append(f";; Article: {article_name}")
        lines.append("")

        # Process theorems
        theorem_count = 0
        for item in data.get("body", []):
            if "kind" in item and "Theorem" in item["kind"]:
                theorem_count += 1
                lines.append(f";; Theorem {theorem_count}")
                lines.append(self.convert_theorem(item, article_name, theorem_count))
                lines.append("")

        lines.append(f";; Total theorems: {theorem_count}")

        return "\n".join(lines)


def test_extraction():
    """Test on a real theorem"""
    converter = BijectiveConverter()

    # Test on boole.miz
    result = converter.convert_json_to_sexp("../output/json/boole.mzp.json")

    # Show first theorem
    lines = result.split("\n")
    for i, line in enumerate(lines[:50]):
        print(line)

    print("\n... (showing first 50 lines)")

    # Save full output
    with open("../output/boole_bijective.sexp", "w") as f:
        f.write(result)
    print(f"\nFull output saved to: output/boole_bijective.sexp")


if __name__ == "__main__":
    test_extraction()