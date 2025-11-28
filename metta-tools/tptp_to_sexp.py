#!/usr/bin/env python3
"""
TPTP to S-Expression Converter

Bijective translation: TPTP Propositional FOF <-> S-expressions
Following the same pattern as Mizar bijection.

Goal: Lossless round-trip conversion with verification.
"""

import re
import json
from typing import List, Dict, Any, Optional
from pathlib import Path


class TPTPToSexp:
    """Convert TPTP FOF propositional problems to S-expressions"""

    def __init__(self):
        self.formulas = []
        self.comments = []
        self.metadata = {}

    def parse_tptp_file(self, filename: str) -> Dict[str, Any]:
        """Parse TPTP file and convert to S-expression structure"""
        with open(filename, 'r') as f:
            content = f.read()

        # Extract metadata from comments
        self._extract_metadata(content)

        # Parse FOF declarations
        self._parse_fof_formulas(content)

        # Build S-expression structure
        return self._build_sexp()

    def _extract_metadata(self, content: str):
        """Extract metadata from TPTP header comments"""
        lines = content.split('\n')
        for line in lines:
            if line.startswith('%'):
                # Extract key-value pairs from comments
                if ':' in line:
                    match = re.match(r'%\s*(\w+)\s*:\s*(.+)', line)
                    if match:
                        key = match.group(1).strip()
                        value = match.group(2).strip()
                        self.metadata[key.lower()] = value
                else:
                    self.comments.append(line[1:].strip())

    def _parse_fof_formulas(self, content: str):
        """Parse all fof(...) and cnf(...) declarations"""
        # Match fof declarations
        fof_pattern = r'fof\(([^,]+),\s*(\w+),\s*(.+?)\)\s*\.'
        matches = re.finditer(fof_pattern, content, re.DOTALL)

        for match in matches:
            name = match.group(1).strip()
            role = match.group(2).strip()
            formula = match.group(3).strip()

            # Parse formula into S-expression
            formula_sexp = self._parse_formula(formula)

            self.formulas.append({
                'name': name,
                'role': role,
                'formula': formula_sexp,
                'type': 'fof'
            })

        # Match cnf declarations
        cnf_pattern = r'cnf\(([^,]+),\s*(\w+),\s*(.+?)\)\s*\.'
        matches = re.finditer(cnf_pattern, content, re.DOTALL)

        for match in matches:
            name = match.group(1).strip()
            role = match.group(2).strip()
            formula = match.group(3).strip()

            # Parse CNF clause (disjunction of literals)
            clause_sexp = self._parse_cnf_clause(formula)

            self.formulas.append({
                'name': name,
                'role': role,
                'formula': clause_sexp,
                'type': 'cnf'
            })

    def _parse_cnf_clause(self, clause_str: str) -> List:
        """
        Parse a CNF clause (disjunction of literals).
        CNF clause: p(X) | ~q(a) | r(f(X))
        Result: (clause (lit (p (var X))) (lit-neg (q (const a))) (lit (r (f (var X)))))
        """
        # Normalize whitespace
        clause_str = ' '.join(clause_str.split())
        clause_str = clause_str.strip()

        # Remove outer parentheses if present
        if clause_str.startswith('(') and clause_str.endswith(')'):
            clause_str = clause_str[1:-1].strip()

        # Split on | at top level
        literals = self._split_clause_literals(clause_str)

        # Parse each literal
        parsed_literals = []
        for lit_str in literals:
            lit_str = lit_str.strip()
            if lit_str.startswith('~'):
                # Negative literal
                atom_str = lit_str[1:].strip()
                atom = self._parse_atom(atom_str)
                parsed_literals.append(['lit-neg', atom])
            else:
                # Positive literal
                atom = self._parse_atom(lit_str)
                parsed_literals.append(['lit', atom])

        return ['clause'] + parsed_literals

    def _split_clause_literals(self, clause_str: str) -> List[str]:
        """Split clause on | respecting parentheses"""
        depth = 0
        literals = []
        current = []

        for char in clause_str:
            if char == '(':
                depth += 1
                current.append(char)
            elif char == ')':
                depth -= 1
                current.append(char)
            elif char == '|' and depth == 0:
                literals.append(''.join(current).strip())
                current = []
            else:
                current.append(char)

        if current:
            literals.append(''.join(current).strip())

        return literals

    def _parse_atom(self, atom_str: str) -> List:
        """
        Parse an atom (predicate with terms).
        Examples: p(X), q(a,b), r(f(X,Y))
        """
        atom_str = atom_str.strip()

        # Check if it has arguments
        if '(' in atom_str and atom_str.endswith(')'):
            paren_pos = atom_str.index('(')
            pred_name = atom_str[:paren_pos].strip()
            args_str = atom_str[paren_pos+1:-1].strip()

            # Parse arguments
            args = self._split_arguments(args_str)
            parsed_args = [self._parse_term(arg.strip()) for arg in args]

            return [pred_name] + parsed_args
        else:
            # Propositional atom (no arguments)
            return [atom_str]

    def _parse_formula(self, formula_str: str) -> List:
        """Parse a TPTP formula string into S-expression"""
        # Normalize whitespace (replace newlines and multiple spaces with single space)
        formula_str = ' '.join(formula_str.split())
        formula_str = formula_str.strip()

        # Handle quantifiers (for future FOL support)
        if formula_str.startswith('!'):
            return self._parse_universal(formula_str)
        if formula_str.startswith('?'):
            return self._parse_existential(formula_str)

        # Handle binary operators (in order of DECREASING precedence)
        # Lower precedence = checked first (outermost operator)

        # Equivalence: <=> (lowest precedence, check BEFORE => to avoid partial match)
        if '<=>' in formula_str:
            parts = self._split_binary(formula_str, '<=>')
            if len(parts) == 2:
                return ['iff',
                       self._parse_formula(parts[0]),
                       self._parse_formula(parts[1])]

        # Implication: =>
        if '=>' in formula_str:
            parts = self._split_binary(formula_str, '=>')
            if len(parts) == 2:
                return ['implies',
                       self._parse_formula(parts[0]),
                       self._parse_formula(parts[1])]

        # Disjunction: |
        if '|' in formula_str:
            parts = self._split_binary(formula_str, '|')
            if len(parts) >= 2:
                # Build right-associative tree for multiple disjunctions
                left = self._parse_formula(parts[0])
                right = self._parse_formula('|'.join(parts[1:])) if len(parts) > 2 else self._parse_formula(parts[1])
                return ['or', left, right]

        # Conjunction: &
        if '&' in formula_str:
            parts = self._split_binary(formula_str, '&')
            if len(parts) >= 2:
                # Build right-associative tree for multiple conjunctions
                left = self._parse_formula(parts[0])
                right = self._parse_formula('&'.join(parts[1:])) if len(parts) > 2 else self._parse_formula(parts[1])
                return ['and', left, right]

        # Inequality: != (check BEFORE = to avoid partial match)
        # Equality has higher precedence, so checked after logical operators
        if '!=' in formula_str:
            parts = self._split_binary(formula_str, '!=')
            if len(parts) == 2:
                return ['not',
                       ['=',
                        self._parse_term(parts[0]),
                        self._parse_term(parts[1])]]

        # Equality: =
        if '=' in formula_str:
            parts = self._split_binary(formula_str, '=')
            if len(parts) == 2:
                return ['=',
                       self._parse_term(parts[0]),
                       self._parse_term(parts[1])]

        # Negation: ~
        if formula_str.startswith('~'):
            return ['not', self._parse_formula(formula_str[1:].strip())]

        # Parentheses (outer grouping)
        if formula_str.startswith('(') and formula_str.endswith(')'):
            return self._parse_formula(formula_str[1:-1].strip())

        # Function/Predicate application: f(t1, t2, ...)
        if '(' in formula_str and formula_str.endswith(')'):
            return self._parse_application(formula_str)

        # Atom (propositional variable or constant)
        return ['atom', formula_str]

    def _split_binary(self, formula: str, operator: str) -> List[str]:
        """Split formula on binary operator, respecting parentheses"""
        depth = 0
        parts = []
        current = []

        i = 0
        while i < len(formula):
            if formula[i] == '(':
                depth += 1
                current.append(formula[i])
            elif formula[i] == ')':
                depth -= 1
                current.append(formula[i])
            elif depth == 0 and formula[i:i+len(operator)] == operator:
                parts.append(''.join(current).strip())
                current = []
                i += len(operator) - 1
            else:
                current.append(formula[i])
            i += 1

        if current:
            parts.append(''.join(current).strip())

        return parts

    def _parse_universal(self, formula_str: str) -> List:
        """Parse universal quantifier: ! [X,Y] : phi"""
        # Extract variables and body
        match = re.match(r'!\s*\[([^\]]+)\]\s*:\s*(.+)', formula_str, re.DOTALL)
        if match:
            vars_str = match.group(1).strip()
            body = match.group(2).strip()
            variables = [v.strip() for v in vars_str.split(',')]
            return ['forall', variables, self._parse_formula(body)]
        return ['atom', formula_str]

    def _parse_existential(self, formula_str: str) -> List:
        """Parse existential quantifier: ? [X,Y] : phi"""
        match = re.match(r'\?\s*\[([^\]]+)\]\s*:\s*(.+)', formula_str, re.DOTALL)
        if match:
            vars_str = match.group(1).strip()
            body = match.group(2).strip()
            variables = [v.strip() for v in vars_str.split(',')]
            return ['exists', variables, self._parse_formula(body)]
        return ['atom', formula_str]

    def _parse_application(self, formula_str: str) -> List:
        """Parse function/predicate application: f(t1, t2, ...)"""
        # Find the function/predicate name and arguments
        paren_pos = formula_str.index('(')
        func_name = formula_str[:paren_pos].strip()
        args_str = formula_str[paren_pos+1:-1].strip()  # Remove outer parens

        # Parse arguments (comma-separated, respecting nested parens)
        args = self._split_arguments(args_str)

        # Recursively parse each argument (could be nested functions/terms)
        parsed_args = [self._parse_term(arg.strip()) for arg in args]

        # Return as S-expression: (func_name arg1 arg2 ...)
        return [func_name] + parsed_args

    def _parse_term(self, term_str: str) -> List:
        """Parse a term (variable, constant, or function application)"""
        term_str = term_str.strip()

        # Function application
        if '(' in term_str and term_str.endswith(')'):
            return self._parse_application(term_str)

        # Variable (uppercase) or constant (lowercase)
        return ['var', term_str] if term_str[0].isupper() else ['const', term_str]

    def _split_arguments(self, args_str: str) -> List[str]:
        """Split comma-separated arguments, respecting nested parentheses"""
        if not args_str:
            return []

        depth = 0
        args = []
        current = []

        for char in args_str:
            if char == '(':
                depth += 1
                current.append(char)
            elif char == ')':
                depth -= 1
                current.append(char)
            elif char == ',' and depth == 0:
                args.append(''.join(current).strip())
                current = []
            else:
                current.append(char)

        if current:
            args.append(''.join(current).strip())

        return args

    def _build_sexp(self) -> Dict[str, Any]:
        """Build complete S-expression structure"""
        return {
            'metadata': self.metadata,
            'comments': self.comments,
            'formulas': self.formulas
        }

    def to_json(self, output_file: str):
        """Write S-expression to JSON file"""
        sexp = self._build_sexp()
        with open(output_file, 'w') as f:
            json.dump(sexp, f, indent=2)

    def to_metta_sexp(self, output_file: str):
        """Write S-expression in MeTTa-style format"""
        sexp = self._build_sexp()
        with open(output_file, 'w') as f:
            f.write(";; TPTP S-Expression Export\n\n")

            # Metadata
            if sexp['metadata']:
                f.write(";; Metadata\n")
                for key, value in sexp['metadata'].items():
                    f.write(f";; {key}: {value}\n")
                f.write("\n")

            # Formulas
            f.write(";; Formulas\n")
            for formula_info in sexp['formulas']:
                f.write(f"\n;; {formula_info['name']} ({formula_info['role']})\n")
                f.write(self._sexp_to_string(
                    ['fof', formula_info['name'], formula_info['role'],
                     formula_info['formula']]
                ))
                f.write("\n")

    def _sexp_to_string(self, sexp: Any, indent: int = 0) -> str:
        """Convert S-expression to string format"""
        if isinstance(sexp, str):
            return sexp
        if not isinstance(sexp, list):
            return str(sexp)
        if len(sexp) == 0:
            return "()"

        # Format as multi-line if nested
        if any(isinstance(x, list) for x in sexp):
            lines = ["("]
            for i, item in enumerate(sexp):
                if i == 0:
                    lines[0] += self._sexp_to_string(item, indent)
                else:
                    lines.append(" " * (indent + 2) + self._sexp_to_string(item, indent + 2))
            lines.append(" " * indent + ")")
            return "\n".join(lines)
        else:
            # Single line
            return "(" + " ".join(str(x) for x in sexp) + ")"


def main():
    """Test the converter on simple_prop.p"""
    import sys
    converter = TPTPToSexp()

    input_file = sys.argv[1] if len(sys.argv) > 1 else 'simple_prop.p'
    sexp = converter.parse_tptp_file(input_file)

    # Output to JSON
    json_file = input_file.replace('.p', '.json')
    converter.to_json(json_file)
    print(f"✅ Created JSON: {json_file}")

    # Output to MeTTa-style S-expression
    metta_file = input_file.replace('.p', '.sexp')
    converter.to_metta_sexp(metta_file)
    print(f"✅ Created S-expression: {metta_file}")

    # Print statistics
    print(f"\n📊 Statistics:")
    print(f"   Formulas: {len(converter.formulas)}")
    for formula in converter.formulas:
        print(f"     - {formula['name']} ({formula['role']})")


if __name__ == '__main__':
    main()
