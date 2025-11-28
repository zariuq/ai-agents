#!/usr/bin/env python3
"""
S-expression to MeTTa Converter

Converts S-expression representation of TPTP FOF formulas to MeTTa backward chainer format.
Uses the S-expression output from tptp_to_sexp.py for full FOF support.
"""

import json
from typing import List, Dict, Any, Union
from pathlib import Path


class SexpToMeTTa:
    """Convert S-expression FOF formulas to MeTTa backward chainer"""

    def __init__(self):
        self.kb_facts = []  # Ground facts for KB
        self.rb_rules = []  # Inference rules for RB
        self.goal = None    # Conjecture to prove

    def load_sexp_file(self, filename: str):
        """Load S-expression JSON file"""
        with open(filename, 'r') as f:
            data = json.load(f)

        formulas = data.get('formulas', [])

        for formula_data in formulas:
            name = formula_data['name']
            role = formula_data['role']
            formula = formula_data['formula']

            if role in ['axiom', 'hypothesis']:
                self._process_axiom(name, formula)
            elif role == 'conjecture':
                self._process_conjecture(name, formula)

    def _process_axiom(self, name: str, formula: Union[List, str]):
        """Process an axiom - could be fact or rule"""
        # If it's an implication at the top level, it's a rule
        if isinstance(formula, list) and formula[0] == 'implies':
            self.rb_rules.append((name, formula))
        # If it's a universal quantifier with an implication inside, it's a rule
        elif isinstance(formula, list) and formula[0] == 'forall':
            body = formula[2]  # Body is third element after ['forall', vars, body]
            if isinstance(body, list) and body[0] == 'implies':
                self.rb_rules.append((name, formula))
            else:
                self.kb_facts.append((name, formula))
        else:
            self.kb_facts.append((name, formula))

    def _process_conjecture(self, name: str, formula: Union[List, str]):
        """Process the conjecture (goal to prove)"""
        self.goal = (name, formula)

    def _sexp_to_metta(self, sexp: Union[List, str], depth: int = 0) -> str:
        """
        Convert S-expression to MeTTa syntax

        S-exp format examples:
        - ['forall', ['X'], body] -> ! [X] : body
        - ['exists', ['Y'], body] -> ? [Y] : body
        - ['implies', p, q] -> (⊢ p q)  for rules, (implies p q) in formulas
        - ['and', p, q] -> (and p q)
        - ['or', p, q] -> (or p q)
        - ['not', p] -> (not p)
        - ['var', 'X'] -> $X
        - ['const', 'a'] -> a
        - ['pred', arg1, arg2] -> (pred arg1 arg2)
        """
        if isinstance(sexp, str):
            return sexp

        if not isinstance(sexp, list) or len(sexp) == 0:
            return str(sexp)

        operator = sexp[0]

        # Quantifiers
        if operator == 'forall' and len(sexp) == 3:
            variables = sexp[1]
            body = self._sexp_to_metta(sexp[2], depth)
            # In MeTTa, we use pattern variables with $
            # For now, we'll convert quantifiers to lambda-like forms
            var_names = ' '.join([f"${v}" for v in variables])
            return f"(forall [{var_names}] {body})"

        if operator == 'exists' and len(sexp) == 3:
            variables = sexp[1]
            body = self._sexp_to_metta(sexp[2], depth)
            var_names = ' '.join([f"${v}" for v in variables])
            return f"(exists [{var_names}] {body})"

        # Logical operators
        if operator == 'implies' and len(sexp) == 3:
            premise = self._sexp_to_metta(sexp[1], depth)
            conclusion = self._sexp_to_metta(sexp[2], depth)
            return f"(implies {premise} {conclusion})"

        if operator == 'and' and len(sexp) == 3:
            left = self._sexp_to_metta(sexp[1], depth)
            right = self._sexp_to_metta(sexp[2], depth)
            return f"(and {left} {right})"

        if operator == 'or' and len(sexp) == 3:
            left = self._sexp_to_metta(sexp[1], depth)
            right = self._sexp_to_metta(sexp[2], depth)
            return f"(or {left} {right})"

        if operator == 'not' and len(sexp) == 2:
            arg = self._sexp_to_metta(sexp[1], depth)
            return f"(not {arg})"

        # Terms
        if operator == 'var' and len(sexp) == 2:
            return f"${sexp[1]}"

        if operator == 'const' and len(sexp) == 2:
            return sexp[1]

        # Predicate/Function application: [pred, arg1, arg2, ...]
        # If first element is a string (predicate name), rest are arguments
        if len(sexp) >= 1:
            pred_name = sexp[0]
            if len(sexp) == 1:
                return pred_name
            else:
                args = [self._sexp_to_metta(arg, depth) for arg in sexp[1:]]
                return f"({pred_name} {' '.join(args)})"

        return str(sexp)

    def generate_metta(self, output_file: str):
        """Generate complete MeTTa backward chainer file"""
        lines = []

        lines.append(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;")
        lines.append(";;; TPTP FOF to MeTTa - Generated via S-expression")
        lines.append(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;")
        lines.append("")

        # Nat for depth control
        lines.append(";;; Nat for depth control")
        lines.append("(: Nat Type)")
        lines.append("(: Z Nat)")
        lines.append("(: S (-> Nat Nat))")
        lines.append("(: fromNumber (-> Number Nat))")
        lines.append("(= (fromNumber $n) (if (<= $n 0) Z (S (fromNumber (- $n 1)))))")
        lines.append("")

        # Knowledge Base
        lines.append(";;; Knowledge Base (Facts)")
        lines.append("!(bind! &kb (new-space))")
        lines.append("")
        for name, formula in self.kb_facts:
            metta_formula = self._sexp_to_metta(formula)
            lines.append(f";; {name}")
            lines.append(f"!(add-atom &kb {metta_formula})")
        lines.append("")

        # Rule Base
        lines.append(";;; Rule Base (Inference Rules)")
        lines.append("!(bind! &rb (new-space))")
        lines.append("")
        for name, formula in self.rb_rules:
            # Extract premise and conclusion from implication
            if isinstance(formula, list):
                if formula[0] == 'implies':
                    premise = self._sexp_to_metta(formula[1])
                    conclusion = self._sexp_to_metta(formula[2])
                    lines.append(f";; {name}")
                    lines.append(f"!(add-atom &rb (⊢ {premise} {conclusion}))")
                elif formula[0] == 'forall':
                    # Universal quantifier with implication inside
                    body = formula[2]
                    if isinstance(body, list) and body[0] == 'implies':
                        premise = self._sexp_to_metta(body[1])
                        conclusion = self._sexp_to_metta(body[2])
                        lines.append(f";; {name}")
                        lines.append(f"!(add-atom &rb (⊢ {premise} {conclusion}))")
        lines.append("")

        # Backward Chainer
        lines.append(";;; Backward Chainer")
        lines.append("(: bc (-> Atom Nat Atom))")
        lines.append("")
        lines.append(";; Base case: match goal against KB")
        lines.append("(= (bc $goal Z)")
        lines.append("   (match &kb $goal $goal))")
        lines.append("")
        lines.append(";; Recursive case: apply rule from RB")
        lines.append("(= (bc $goal (S $k))")
        lines.append("   (match &rb")
        lines.append("     (⊢ $premise $goal)")
        lines.append("     (let $premise (bc $premise $k)")
        lines.append("       $goal)))")
        lines.append("")

        # Goal Query
        if self.goal:
            goal_name, goal_formula = self.goal
            goal_metta = self._sexp_to_metta(goal_formula)
            lines.append(";;; Query (Prove the conjecture)")
            lines.append(f"; Proving: {goal_name}")
            lines.append(f"!(bc {goal_metta} (fromNumber 5))")
            lines.append("")

        # Write to file
        with open(output_file, 'w') as f:
            f.write("\n".join(lines))

        print(f"✅ Generated MeTTa file: {output_file}")
        print(f"   KB Facts: {len(self.kb_facts)}")
        print(f"   RB Rules: {len(self.rb_rules)}")
        print(f"   Goal: {self.goal[0] if self.goal else 'None'}")


def main():
    """Test with simple propositional problem"""
    import sys

    if len(sys.argv) < 2:
        print("Usage: python3 sexp_to_metta.py <sexp_json_file>")
        print("Example: python3 sexp_to_metta.py simple_prop_1.json")
        sys.exit(1)

    sexp_file = sys.argv[1]
    output_file = sexp_file.replace('_1.json', '.metta')

    converter = SexpToMeTTa()
    converter.load_sexp_file(sexp_file)
    converter.generate_metta(output_file)


if __name__ == '__main__':
    main()
