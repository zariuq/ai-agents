#!/usr/bin/env python3
"""
S-Expression to TPTP Converter

Reverse converter: S-expressions -> TPTP FOF
For bijective round-trip verification.
"""

import json
from typing import List, Dict, Any, Union


class SexpToTPTP:
    """Convert S-expressions back to TPTP FOF format"""

    def __init__(self):
        pass

    def load_from_json(self, json_file: str) -> Dict[str, Any]:
        """Load S-expression from JSON file"""
        with open(json_file, 'r') as f:
            return json.load(f)

    def load_from_sexp(self, sexp_file: str) -> Dict[str, Any]:
        """Load S-expression from MeTTa-style file"""
        # For now, use JSON format
        # Could implement proper S-expression parser later
        json_file = sexp_file.replace('.sexp', '.json')
        return self.load_from_json(json_file)

    def convert_to_tptp(self, sexp_data: Dict[str, Any], output_file: str):
        """Convert S-expression back to TPTP format"""
        with open(output_file, 'w') as f:
            # Write header comments
            f.write("%"  + "-" * 77 + "\n")

            # Write metadata
            metadata = sexp_data.get('metadata', {})
            if 'file' in metadata:
                f.write(f"% File     : {metadata['file']}\n")
            if 'domain' in metadata:
                f.write(f"% Domain   : {metadata['domain']}\n")
            if 'problem' in metadata:
                f.write(f"% Problem  : {metadata['problem']}\n")
            if 'english' in metadata:
                f.write(f"% English  : {metadata['english']}\n")

            f.write("%"  + "-" * 77 + "\n")
            f.write("\n")

            # Write formulas
            for formula_info in sexp_data.get('formulas', []):
                name = formula_info['name']
                role = formula_info['role']
                formula_sexp = formula_info['formula']
                formula_type = formula_info.get('type', 'fof')

                if formula_type == 'cnf':
                    # Convert CNF clause
                    clause_str = self._cnf_to_tptp(formula_sexp)
                    f.write(f"cnf({name},{role},\n")
                    f.write(f"    {clause_str} ).\n")
                else:
                    # Convert FOF formula
                    formula_str = self._sexp_to_tptp(formula_sexp)
                    f.write(f"fof({name},{role},\n")
                    f.write(f"    {formula_str} ).\n")
                f.write("\n")

            f.write("%"  + "-" * 77 + "\n")

    def _cnf_to_tptp(self, sexp: Union[List, str]) -> str:
        """
        Convert CNF clause S-expression to TPTP string.
        Input: ['clause', ['lit', atom1], ['lit-neg', atom2], ...]
        Output: "atom1 | ~atom2 | ..."
        """
        if not isinstance(sexp, list) or len(sexp) == 0:
            return ""

        if sexp[0] != 'clause':
            return str(sexp)

        # Process literals
        literals = []
        for lit_sexp in sexp[1:]:
            if not isinstance(lit_sexp, list) or len(lit_sexp) != 2:
                continue

            lit_type = lit_sexp[0]
            atom = lit_sexp[1]

            # Convert atom to string
            atom_str = self._atom_to_tptp(atom)

            if lit_type == 'lit':
                literals.append(atom_str)
            elif lit_type == 'lit-neg':
                literals.append(f"~{atom_str}")

        # Join with |
        if len(literals) == 0:
            return "$false"  # Empty clause
        elif len(literals) == 1:
            return literals[0]
        else:
            return "(" + " | ".join(literals) + ")"

    def _atom_to_tptp(self, atom: Union[List, str]) -> str:
        """
        Convert atom S-expression to TPTP string.
        Input: ['predname', term1, term2, ...]
        Output: "predname(term1, term2, ...)"
        """
        if isinstance(atom, str):
            return atom

        if not isinstance(atom, list) or len(atom) == 0:
            return ""

        pred_name = atom[0]
        if len(atom) == 1:
            # Propositional atom
            return pred_name
        else:
            # Predicate with arguments
            args = [self._sexp_to_tptp(arg) for arg in atom[1:]]
            args_str = ",".join(args)
            return f"{pred_name}({args_str})"

    def _sexp_to_tptp(self, sexp: Union[List, str]) -> str:
        """Convert S-expression formula to TPTP string"""
        if isinstance(sexp, str):
            return sexp

        if not isinstance(sexp, list) or len(sexp) == 0:
            return ""

        operator = sexp[0]

        # Atom
        if operator == 'atom' and len(sexp) == 2:
            return sexp[1]

        # Negation
        if operator == 'not' and len(sexp) == 2:
            inner = self._sexp_to_tptp(sexp[1])
            if self._needs_parens(sexp[1]):
                return f"~ ({inner})"
            return f"~ {inner}"

        # Binary operators
        if operator == 'implies' and len(sexp) == 3:
            left = self._sexp_to_tptp(sexp[1])
            right = self._sexp_to_tptp(sexp[2])
            return f"( {left} => {right} )"

        if operator == 'iff' and len(sexp) == 3:
            left = self._sexp_to_tptp(sexp[1])
            right = self._sexp_to_tptp(sexp[2])
            return f"( {left} <=> {right} )"

        if operator == 'and' and len(sexp) == 3:
            left = self._sexp_to_tptp(sexp[1])
            right = self._sexp_to_tptp(sexp[2])
            return f"( {left} & {right} )"

        if operator == 'or' and len(sexp) == 3:
            left = self._sexp_to_tptp(sexp[1])
            right = self._sexp_to_tptp(sexp[2])
            return f"( {left} | {right} )"

        # Equality
        if operator == '=' and len(sexp) == 3:
            left = self._sexp_to_tptp(sexp[1])
            right = self._sexp_to_tptp(sexp[2])
            return f"{left} = {right}"

        # Quantifiers
        if operator == 'forall' and len(sexp) == 3:
            variables = sexp[1]
            body = self._sexp_to_tptp(sexp[2])
            vars_str = ",".join(variables)
            return f"! [{vars_str}] : {body}"

        if operator == 'exists' and len(sexp) == 3:
            variables = sexp[1]
            body = self._sexp_to_tptp(sexp[2])
            vars_str = ",".join(variables)
            return f"? [{vars_str}] : {body}"

        # Terms: variables and constants
        if operator == 'var' and len(sexp) == 2:
            return sexp[1]

        if operator == 'const' and len(sexp) == 2:
            return sexp[1]

        # Predicate/Function application: (pred_name arg1 arg2 ...)
        # This is the general case for anything not matched above
        # e.g., (human (var X)) -> human(X)
        #       (f (var X) (const a)) -> f(X,a)
        if len(sexp) >= 1:
            func_name = sexp[0]
            if len(sexp) == 1:
                # Nullary predicate/constant
                return func_name
            else:
                # N-ary predicate/function
                args = [self._sexp_to_tptp(arg) for arg in sexp[1:]]
                args_str = ",".join(args)
                return f"{func_name}({args_str})"

        # Unknown operator
        return str(sexp)

    def _needs_parens(self, sexp: Union[List, str]) -> bool:
        """Check if S-expression needs parentheses when negated"""
        if isinstance(sexp, str):
            return False
        if not isinstance(sexp, list) or len(sexp) == 0:
            return False
        operator = sexp[0]
        # Binary operators need parens (including equality)
        return operator in ['implies', 'iff', 'and', 'or', '=']


def main():
    """Test reverse conversion"""
    import sys
    converter = SexpToTPTP()

    # Get input/output files from command line
    if len(sys.argv) < 2:
        print("Usage: python3 sexp_to_tptp.py <input.json> [output.p]")
        print("Example: python3 sexp_to_tptp.py socrates_fof.json socrates_reconstructed.p")
        sys.exit(1)

    json_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else json_file.replace('.json', '_reconstructed.p')

    # Load S-expression
    sexp_data = converter.load_from_json(json_file)

    # Convert back to TPTP
    converter.convert_to_tptp(sexp_data, output_file)

    print(f"✅ Reconstructed TPTP file: {output_file}")
    print(f"\n📊 Formulas converted: {len(sexp_data.get('formulas', []))}")


if __name__ == '__main__':
    main()
