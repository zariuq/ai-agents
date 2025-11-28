#!/usr/bin/env python3
"""
Reverse translator: S-expression → Mizar (FIXED VERSION)
For bijective round-trip verification
"""

import sys
import re
from typing import Any, List, Union

class SexpToMizar:
    """Convert S-expressions back to Mizar syntax"""

    def __init__(self):
        self.indent_level = 0

    def parse_sexp(self, text: str) -> List:
        """Parse S-expression string into nested lists"""
        text = text.strip()
        if not text or text.startswith(';;'):
            return []

        tokens = []
        i = 0
        while i < len(text):
            if text[i] in '()':
                tokens.append(text[i])
                i += 1
            elif text[i] in ' \t\n\r':
                i += 1
            elif text[i] == '"':
                # String literal
                j = i + 1
                while j < len(text) and text[j] != '"':
                    if text[j] == '\\':
                        j += 2
                    else:
                        j += 1
                tokens.append(text[i:j+1])
                i = j + 1
            elif text[i] == '[':
                # Array literal
                j = i + 1
                depth = 1
                while j < len(text) and depth > 0:
                    if text[j] == '[':
                        depth += 1
                    elif text[j] == ']':
                        depth -= 1
                    j += 1
                tokens.append(text[i:j])
                i = j
            else:
                # Atom
                j = i
                while j < len(text) and text[j] not in '() \t\n\r"[]':
                    j += 1
                tokens.append(text[i:j])
                i = j

        # Build tree
        stack = [[]]
        for token in tokens:
            if token == '(':
                new_list = []
                stack[-1].append(new_list)
                stack.append(new_list)
            elif token == ')':
                if len(stack) > 1:
                    stack.pop()
            else:
                stack[-1].append(token)

        return stack[0][0] if stack[0] else []

    def _extract_attributes(self, attrs) -> List[str]:
        """Recursively extract attribute names from nested structure"""
        result = []

        if not isinstance(attrs, list):
            return result

        for attr in attrs:
            if isinstance(attr, list):
                if len(attr) == 0:
                    continue

                op = attr[0]

                if op == "attr" and len(attr) > 2:
                    # Direct attribute: (attr SYM "NAME")
                    result.append(attr[2].strip('"'))

                elif op == "non":
                    # Negated attribute: (non ((attr ...)))
                    # The inner part is wrapped in another list
                    if len(attr) > 1 and isinstance(attr[1], list):
                        inner_attrs = self._extract_attributes(attr[1])
                        for inner in inner_attrs:
                            result.append(f"non {inner}")
                else:
                    # Try to recurse
                    result.extend(self._extract_attributes(attr))

        return result

    def convert_term(self, sexp) -> str:
        """Convert term S-expression to Mizar"""
        if isinstance(sexp, str):
            # Handle quoted strings
            if sexp.startswith('"') and sexp.endswith('"'):
                return sexp[1:-1]
            return sexp

        if not isinstance(sexp, list) or len(sexp) == 0:
            return ""

        op = sexp[0]

        if op == "var":
            # Variable: (var "X" :pos [...])
            name = sexp[1].strip('"') if len(sexp) > 1 else ""
            return name

        elif op == "empty-set":
            return "{}"

        elif op == "infix":
            # Infix operator: (infix SYM "SPELLING" ARG1 ARG2)
            if len(sexp) >= 5:
                spelling = sexp[2].strip('"')
                arg1 = self.convert_term(sexp[3])
                arg2 = self.convert_term(sexp[4])
                return f"({arg1} {spelling} {arg2})"
            return ""

        elif op == "func":
            # Function: (func SYM "SPELLING" (ARGS...))
            if len(sexp) >= 3:
                spelling = sexp[2].strip('"')
                if len(sexp) > 3 and isinstance(sexp[3], list):
                    args = [self.convert_term(arg) for arg in sexp[3]]
                    if args:
                        return f"{spelling}({', '.join(args)})"
                return spelling
            return ""

        elif op == "num":
            return str(sexp[1]) if len(sexp) > 1 else "0"

        return str(sexp)

    def convert_formula(self, sexp) -> str:
        """Convert formula S-expression to Mizar"""
        if isinstance(sexp, str):
            return sexp

        if not isinstance(sexp, list) or len(sexp) == 0:
            return ""

        op = sexp[0]

        if op == "forall":
            # Universal: (forall ((VARS (mode ...))) (such-that ...) BODY)
            vars_list = sexp[1] if len(sexp) > 1 else []

            # Extract variable names and types
            var_decls = []
            if isinstance(vars_list, list):
                for var_group in vars_list:
                    if isinstance(var_group, list):
                        names = []
                        type_name = "set"
                        for item in var_group:
                            if isinstance(item, str):
                                names.append(item.strip('"'))
                            elif isinstance(item, list) and len(item) > 2 and item[0] == "mode":
                                type_name = item[2].strip('"')
                        if names:
                            var_decls.append(f"{', '.join(names)} being {type_name}")

            vars_str = ", ".join(var_decls)

            # Check for such-that clause
            body_idx = 2
            st_clause = ""
            if len(sexp) > 2 and isinstance(sexp[2], list) and sexp[2][0] == "such-that":
                if len(sexp[2]) > 1:
                    st_clause = " st " + self.convert_formula(sexp[2][1])
                body_idx = 3

            # Get body formula
            body = self.convert_formula(sexp[body_idx]) if len(sexp) > body_idx else "thesis"

            return f"for {vars_str}{st_clause} holds {body}"

        elif op == "exists" or op == "ex":
            # Existential: (ex ((VARS ...)) BODY)
            vars_list = sexp[1] if len(sexp) > 1 else []
            var_names = []
            if isinstance(vars_list, list):
                for var_group in vars_list:
                    if isinstance(var_group, list):
                        for item in var_group:
                            if isinstance(item, str):
                                var_names.append(item.strip('"'))

            body = self.convert_formula(sexp[2]) if len(sexp) > 2 else "thesis"
            return f"ex {', '.join(var_names)} st {body}"

        elif op == "pred-infix":
            # Infix predicate: (pred-infix +/- SYM "SPELLING" ARG1 ARG2)
            if len(sexp) >= 6:
                positive = sexp[1] == "+"
                spelling = sexp[3].strip('"')
                arg1 = self.convert_term(sexp[4])
                arg2 = self.convert_term(sexp[5])
                neg = "not " if not positive else ""
                return f"{neg}{arg1} {spelling} {arg2}"
            return ""

        elif op == "attr":
            # Attribute: (attr +/- TERM ((attr ...) (non ((attr ...)))))
            if len(sexp) >= 4:
                positive = sexp[1] == "+"
                term = self.convert_term(sexp[2])
                attrs = sexp[3]

                # Extract attribute names recursively
                attr_names = self._extract_attributes(attrs)
                attr_str = " ".join(attr_names)
                return f"{term} is {attr_str}"
            return ""

        elif op == "and":
            left = self.convert_formula(sexp[1]) if len(sexp) > 1 else ""
            right = self.convert_formula(sexp[2]) if len(sexp) > 2 else ""
            return f"({left} & {right})"

        elif op == "or":
            left = self.convert_formula(sexp[1]) if len(sexp) > 1 else ""
            right = self.convert_formula(sexp[2]) if len(sexp) > 2 else ""
            return f"({left} or {right})"

        elif op == "implies":
            left = self.convert_formula(sexp[1]) if len(sexp) > 1 else ""
            right = self.convert_formula(sexp[2]) if len(sexp) > 2 else ""
            return f"({left} implies {right})"

        elif op == "not":
            inner = self.convert_formula(sexp[1]) if len(sexp) > 1 else ""
            return f"not {inner}"

        return str(sexp)

    def convert_justification(self, sexp) -> str:
        """Convert justification to Mizar"""
        if not isinstance(sexp, list) or len(sexp) == 0:
            return ""

        op = sexp[0]

        if op == "by":
            # Extract references
            refs = []
            if len(sexp) > 1 and isinstance(sexp[1], list):
                for ref in sexp[1]:
                    if isinstance(ref, list) and ref[0] == "ref":
                        if len(ref) == 2:
                            # Local reference
                            refs.append(ref[1].strip('"'))
                        elif len(ref) >= 3:
                            # Article reference
                            article = ref[2].strip('"')
                            refs.append(article)
            return f"by {', '.join(refs)}" if refs else ""

        elif op == "proof-block":
            # Full proof - just indicate it exists
            return "proof\n  ...\nend"

        return ""

    def convert_theorem(self, sexp) -> str:
        """Convert theorem S-expression to Mizar"""
        if not isinstance(sexp, list) or len(sexp) < 2 or sexp[0] != "theorem":
            return ""

        lines = []

        # Extract label (index 1)
        label = sexp[1].strip('"') if len(sexp) > 1 else ""

        # Find formula (skip :pos and position if present)
        formula_idx = 2
        if len(sexp) > 2 and sexp[2] == ":pos":
            formula_idx = 4

        # Extract formula
        if len(sexp) > formula_idx:
            formula = self.convert_formula(sexp[formula_idx])
            lines.append("theorem")
            lines.append(f"  {formula}")

            # Extract justification if present
            just_idx = formula_idx + 1
            if len(sexp) > just_idx:
                just = self.convert_justification(sexp[just_idx])
                if just:
                    if just.startswith("proof"):
                        lines.append(just)
                    else:
                        lines.append(f"  {just};")
                else:
                    lines.append(";")
            else:
                lines.append(";")

        return "\n".join(lines)

    def convert_file(self, input_file: str) -> str:
        """Convert S-expression file to Mizar"""
        with open(input_file, 'r') as f:
            content = f.read()

        results = []

        # Accumulate complete S-expressions (handle multi-line)
        current_sexp = ""
        paren_depth = 0

        for line in content.split('\n'):
            stripped = line.strip()

            # Skip comments
            if stripped.startswith(';;'):
                continue

            if stripped:
                current_sexp += " " + stripped
                paren_depth += stripped.count('(') - stripped.count(')')

                # Complete S-expression when parens balance
                if paren_depth == 0 and current_sexp.strip():
                    complete = current_sexp.strip()
                    if complete.startswith('(theorem'):
                        sexp = self.parse_sexp(complete)
                        if sexp:
                            mizar = self.convert_theorem(sexp)
                            if mizar:
                                results.append(mizar)
                                results.append("")
                    current_sexp = ""

        return "\n".join(results)


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 sexp_to_mizar_v2.py <sexp_file>")
        sys.exit(1)

    converter = SexpToMizar()
    result = converter.convert_file(sys.argv[1])
    print(result)


if __name__ == "__main__":
    main()
