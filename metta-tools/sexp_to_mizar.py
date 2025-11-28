#!/usr/bin/env python3
"""
Reverse translator: S-expression → Mizar
For bijective round-trip verification
"""

import re
import json
from typing import Any, Dict, List, Union, Tuple

class SexpToMizar:
    """
    Convert S-expressions back to Mizar syntax.
    This enables round-trip verification of our translation.
    """

    def __init__(self):
        self.indent_level = 0
        self.indent_size = 2

    def indent(self):
        """Return current indentation"""
        return " " * (self.indent_level * self.indent_size)

    def parse_sexp(self, sexp: str) -> List:
        """Parse S-expression string into nested lists"""
        # Simple S-expression parser
        sexp = sexp.strip()
        if not sexp:
            return []

        result = []
        stack = [result]
        current_token = ""
        in_string = False
        escape_next = False

        for char in sexp:
            if escape_next:
                current_token += char
                escape_next = False
            elif char == '\\' and in_string:
                escape_next = True
                current_token += char
            elif char == '"':
                if in_string:
                    # End of string
                    stack[-1].append(current_token)
                    current_token = ""
                    in_string = False
                else:
                    # Start of string
                    in_string = True
            elif in_string:
                current_token += char
            elif char == '(':
                # Start new list
                new_list = []
                stack[-1].append(new_list)
                stack.append(new_list)
            elif char == ')':
                # End current list
                if current_token:
                    stack[-1].append(current_token)
                    current_token = ""
                if len(stack) > 1:
                    stack.pop()
            elif char in ' \t\n\r':
                # Whitespace - end current token
                if current_token:
                    stack[-1].append(current_token)
                    current_token = ""
            else:
                current_token += char

        if current_token:
            stack[-1].append(current_token)

        return result[0] if result else []

    def sexp_to_formula(self, sexp: List) -> str:
        """Convert S-expression formula to Mizar syntax"""
        if not sexp:
            return ""

        op = sexp[0]

        # Universal quantifier
        if op == "forall":
            vars = sexp[1]
            var_decls = []

            # Parse variable declarations
            for var_group in vars:
                if isinstance(var_group, list):
                    # Multiple vars with same type
                    var_names = []
                    type_info = None
                    for item in var_group:
                        if isinstance(item, str):
                            var_names.append(item)
                        elif isinstance(item, list) and item[0] == "mode":
                            type_info = item[2]  # The type spelling

                    if var_names:
                        if type_info:
                            var_decls.append(f"{', '.join(var_names)} being {type_info}")
                        else:
                            var_decls.append(', '.join(var_names))

            vars_str = ", ".join(var_decls) if var_decls else ""

            # Check for 'such-that' clause
            body_start = 2
            such_that = ""
            if len(sexp) > 2 and isinstance(sexp[2], list) and sexp[2][0] == "such-that":
                such_that = " st " + self.sexp_to_formula(sexp[2][1]) if len(sexp[2]) > 1 else ""
                body_start = 3

            # Get the main formula
            if len(sexp) > body_start:
                body = self.sexp_to_formula(sexp[body_start])
            else:
                body = "thesis"

            return f"for {vars_str}{such_that} holds {body}"

        # Existential quantifier
        elif op == "exists":
            vars = sexp[1]
            var_names = []
            for var_group in vars:
                if isinstance(var_group, list):
                    for item in var_group:
                        if isinstance(item, str):
                            var_names.append(item)

            vars_str = ", ".join(var_names)

            # Get body
            body = self.sexp_to_formula(sexp[2]) if len(sexp) > 2 else "thesis"
            return f"ex {vars_str} st {body}"

        # Binary operations
        elif op == "and":
            left = self.sexp_to_formula(sexp[1]) if len(sexp) > 1 else ""
            right = self.sexp_to_formula(sexp[2]) if len(sexp) > 2 else ""
            return f"{left} & {right}"

        elif op == "or":
            left = self.sexp_to_formula(sexp[1]) if len(sexp) > 1 else ""
            right = self.sexp_to_formula(sexp[2]) if len(sexp) > 2 else ""
            return f"{left} or {right}"

        elif op == "implies":
            left = self.sexp_to_formula(sexp[1]) if len(sexp) > 1 else ""
            right = self.sexp_to_formula(sexp[2]) if len(sexp) > 2 else ""
            return f"{left} implies {right}"

        elif op == "iff":
            left = self.sexp_to_formula(sexp[1]) if len(sexp) > 1 else ""
            right = self.sexp_to_formula(sexp[2]) if len(sexp) > 2 else ""
            return f"{left} iff {right}"

        elif op == "not":
            inner = self.sexp_to_formula(sexp[1]) if len(sexp) > 1 else ""
            return f"not {inner}"

        # Predicates
        elif op == "pred-infix":
            # Infix predicate like =, in, c=
            positive = sexp[1] == "+"
            _sym = sexp[2]
            spelling = sexp[3].strip('"')

            # Get arguments
            if len(sexp) >= 6:
                arg1 = self.sexp_to_term(sexp[4])
                arg2 = self.sexp_to_term(sexp[5])
                neg = "not " if not positive else ""
                return f"{neg}{arg1} {spelling} {arg2}"
            return ""

        elif op == "pred":
            # Prefix predicate
            positive = sexp[1] == "+"
            _sym = sexp[2]
            spelling = sexp[3].strip('"')
            args = [self.sexp_to_term(arg) for arg in sexp[4:]]
            args_str = ", ".join(args) if args else ""
            neg = "not " if not positive else ""
            return f"{neg}{spelling}({args_str})" if args_str else f"{neg}{spelling}"

        # Attributes
        elif op == "attr":
            positive = sexp[1] == "+"
            term = self.sexp_to_term(sexp[2]) if len(sexp) > 2 else ""
            attrs = sexp[3] if len(sexp) > 3 else []

            attr_str = self.attrs_to_mizar(attrs)
            neg = "non " if not positive else ""
            return f"{term} is {neg}{attr_str}"

        # Type predicate
        elif op == "is":
            positive = sexp[1] == "+"
            term = self.sexp_to_term(sexp[2]) if len(sexp) > 2 else ""
            ty = self.type_to_mizar(sexp[3]) if len(sexp) > 3 else "set"
            neg = "not " if not positive else ""
            return f"{neg}{term} is {ty}"

        # Constants
        elif op == "true":
            return "thesis"
        elif op == "false":
            return "contradiction"

        else:
            # Unknown - try to convert as-is
            if isinstance(sexp, list):
                parts = [str(s) for s in sexp]
                return " ".join(parts)
            else:
                return str(sexp)

    def sexp_to_term(self, sexp) -> str:
        """Convert S-expression term to Mizar syntax"""
        if isinstance(sexp, str):
            return sexp

        if not sexp or not isinstance(sexp, list):
            return ""

        op = sexp[0]

        # Variable
        if op == "var":
            name = sexp[1].strip('"') if len(sexp) > 1 else ""
            # Ignore position info
            return name

        # Constant
        elif op == "const":
            # Just return a placeholder or the const id
            return f"the Element"

        # Number
        elif op == "num":
            return str(sexp[1]) if len(sexp) > 1 else "0"

        # Infix operation
        elif op == "infix":
            _sym = sexp[1]
            spelling = sexp[2].strip('"')

            # Special case for empty set
            if spelling == "{}" and len(sexp) == 3:
                return "{}"

            if len(sexp) >= 5:
                arg1 = self.sexp_to_term(sexp[3])
                arg2 = self.sexp_to_term(sexp[4])
                return f"{arg1} {spelling} {arg2}"
            return ""

        # Empty set
        elif op == "empty-set":
            return "{}"

        # Function
        elif op == "func":
            _sym = sexp[1]
            spelling = sexp[2].strip('"')
            args_list = sexp[3] if len(sexp) > 3 else []

            if isinstance(args_list, list):
                args = [self.sexp_to_term(arg) for arg in args_list]
                args_str = ", ".join(args) if args else ""
                return f"{spelling}({args_str})" if args_str else spelling
            return spelling

        # Bracket notation
        elif op == "bracket":
            lsym = sexp[1].strip('"')
            rsym = sexp[2].strip('"')
            args_list = sexp[3] if len(sexp) > 3 else []

            if isinstance(args_list, list):
                args = [self.sexp_to_term(arg) for arg in args_list]
                args_str = ", ".join(args) if args else ""
                return f"{lsym}{args_str}{rsym}"
            return f"{lsym}{rsym}"

        # The 'it' keyword
        elif op == "it":
            return "it"

        else:
            # Unknown term
            return str(sexp)

    def attrs_to_mizar(self, attrs) -> str:
        """Convert attribute list to Mizar syntax"""
        if not attrs or attrs == "no-attrs":
            return ""

        if isinstance(attrs, list):
            result = []
            for attr in attrs:
                if isinstance(attr, list):
                    if attr[0] == "attr":
                        spelling = attr[2].strip('"') if len(attr) > 2 else ""
                        result.append(spelling)
                    elif attr[0] == "non":
                        inner = self.attrs_to_mizar([attr[1]]) if len(attr) > 1 else ""
                        result.append(f"non {inner}")
            return " ".join(result)
        return ""

    def type_to_mizar(self, ty) -> str:
        """Convert type to Mizar syntax"""
        if not ty or ty == "any-type":
            return "set"

        if isinstance(ty, list):
            if ty[0] == "mode":
                spelling = ty[2].strip('"') if len(ty) > 2 else "set"
                return spelling
            elif ty[0] == "struct":
                # Structured type - needs more work
                return "set"

        return "set"

    def justification_to_mizar(self, just) -> str:
        """Convert justification to Mizar syntax"""
        if not just or just == ["no-justification"]:
            return ""

        if not isinstance(just, list):
            return ""

        op = just[0]

        if op == "by":
            refs = just[1] if len(just) > 1 else []
            ref_str = self.refs_to_mizar(refs)
            return f"by {ref_str}" if ref_str else ""

        elif op == "from":
            scheme = self.refs_to_mizar([just[1]]) if len(just) > 1 else ""
            refs = self.refs_to_mizar(just[2]) if len(just) > 2 else ""
            return f"from {scheme}({refs})"

        elif op == "proof-block":
            # Full proof block
            return "proof\n  ...\nend"

        return ""

    def refs_to_mizar(self, refs) -> str:
        """Convert reference list to Mizar syntax"""
        if not refs or refs == "no-refs":
            return ""

        result = []
        if isinstance(refs, list):
            for ref in refs:
                if isinstance(ref, list):
                    if ref[0] == "ref":
                        if len(ref) == 2:
                            # Local reference like "Lm1"
                            result.append(ref[1])
                        elif len(ref) >= 4:
                            # Article reference
                            art = ref[1]
                            spelling = ref[2].strip('"') if isinstance(ref[2], str) else ""
                            inner_refs = ref[3] if len(ref) > 3 else []

                            # Parse inner references
                            inner_parts = []
                            if isinstance(inner_refs, list):
                                for inner in inner_refs:
                                    if isinstance(inner, list):
                                        if inner[0] == "thm":
                                            inner_parts.append(f"{inner[1]}")
                                        elif inner[0] == "def":
                                            inner_parts.append(f"def {inner[1]}")

                            if inner_parts:
                                ref_str = f"{spelling}:{','.join(inner_parts)}"
                            else:
                                ref_str = spelling
                            result.append(ref_str)

        return ", ".join(result)

    def sexp_theorem_to_mizar(self, sexp: List) -> str:
        """Convert a theorem S-expression to Mizar syntax"""
        if not sexp or sexp[0] != "theorem":
            return ""

        lines = []

        # Extract position if present
        pos = None
        formula_index = 1
        just_index = 2

        if len(sexp) > 1 and sexp[1] == ":pos":
            pos = sexp[2]
            formula_index = 3
            just_index = 4

        # Add position comment
        if pos:
            lines.append(f":: Line {pos[0]}")

        lines.append("theorem")

        # Extract and convert formula
        if len(sexp) > formula_index:
            formula = self.sexp_to_formula(sexp[formula_index])
            self.indent_level = 1
            lines.append(f"{self.indent()}{formula}")
            self.indent_level = 0

        # Extract and convert justification
        if len(sexp) > just_index:
            just = self.justification_to_mizar(sexp[just_index])
            if just:
                if just.startswith("proof"):
                    lines.append(just)
                else:
                    lines.append(f"{self.indent()}{just};")
            else:
                lines.append(";")
        else:
            lines.append(";")

        return "\n".join(lines)

    def convert_sexp_file(self, sexp_file: str) -> str:
        """Convert an S-expression file back to Mizar"""
        with open(sexp_file, 'r') as f:
            content = f.read()

        # Parse all theorems
        lines = []

        # Skip comments
        for line in content.split('\n'):
            if line.startswith(';;'):
                continue

            if line.startswith('(theorem'):
                # Find the complete theorem (might span multiple lines)
                # This is simplified - real parser would handle nested parens
                theorem_lines = [line]
                paren_count = line.count('(') - line.count(')')

                # For now, just parse single-line theorems
                # Real implementation would handle multi-line
                sexp = self.parse_sexp(line)
                if sexp:
                    mizar = self.sexp_theorem_to_mizar(sexp)
                    if mizar:
                        lines.append(mizar)
                        lines.append("")

        return "\n".join(lines)


def test_reverse_translation():
    """Test the reverse translator"""
    converter = SexpToMizar()

    # Test simple formula
    test_sexp = ['forall', [['X', ['mode', 0, 'set']]],
                 ['pred-infix', '+', 0, '=',
                  ['infix', 1, '\\/', ['var', 'X'], ['empty-set']],
                  ['var', 'X']]]

    result = converter.sexp_to_formula(test_sexp)
    print("Test formula:")
    print(f"  S-expr: {test_sexp}")
    print(f"  Mizar:  {result}")
    print()

    # Expected: "for X being set holds X \\/ {} = X"

    # Test with such-that clause
    test_sexp2 = ['forall', [['x', 'X', ['mode', 0, 'set']]],
                  ['such-that', ['pred-infix', '+', 2, 'in', ['var', 'x'], ['var', 'X']]],
                  ['attr', '+', ['var', 'X'], [['non', [['attr', 1, 'empty']]]]]]

    result2 = converter.sexp_to_formula(test_sexp2)
    print("Test with such-that:")
    print(f"  Mizar:  {result2}")
    print()

    # Expected: "for x, X being set st x in X holds X is non empty"

    print("Reverse translator created successfully!")
    print("Ready for round-trip testing.")


if __name__ == "__main__":
    test_reverse_translation()