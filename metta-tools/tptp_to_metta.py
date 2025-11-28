#!/usr/bin/env python3
"""
TPTP to MeTTa Converter

Converts TPTP FOF (First-Order Form) problems to MeTTa backward chainer format.
Demonstrates how MUCH easier TPTP is than Mizar!
"""

import re
from pathlib import Path
from typing import List, Tuple, Optional

class TPTPToMeTTa:
    """Convert TPTP FOF to MeTTa"""

    def __init__(self):
        self.kb_facts = []  # Knowledge base facts
        self.rb_rules = []  # Rule base (inference rules)
        self.goal = None    # Conjecture to prove

    def parse_fof_file(self, filename: str):
        """Parse a TPTP file containing FOF formulas"""
        with open(filename, 'r') as f:
            content = f.read()

        # Extract all fof declarations
        fof_pattern = r'fof\(([^,]+),\s*(\w+),\s*(.+?)\)\s*\.'
        matches = re.finditer(fof_pattern, content, re.DOTALL)

        for match in matches:
            name = match.group(1).strip()
            role = match.group(2).strip()  # axiom, conjecture, hypothesis, etc.
            formula = match.group(3).strip()

            if role == 'axiom' or role == 'hypothesis':
                self._process_axiom(name, formula)
            elif role == 'conjecture':
                self._process_conjecture(name, formula)

    def _process_axiom(self, name: str, formula: str):
        """Process an axiom - could be fact or rule"""
        # Simple heuristic: if it contains '=>', it's a rule; otherwise it's a fact
        if '=>' in formula:
            self.rb_rules.append((name, formula))
        else:
            self.kb_facts.append((name, formula))

    def _process_conjecture(self, name: str, formula: str):
        """Process the conjecture (goal to prove)"""
        self.goal = (name, formula)

    def _convert_formula(self, formula: str) -> str:
        """Convert TPTP formula to MeTTa S-expression"""
        # Simple propositional conversion for now
        formula = formula.strip()

        # Handle implication: p => q becomes (implies p q)
        if '=>' in formula:
            parts = formula.split('=>')
            if len(parts) == 2:
                antecedent = self._convert_formula(parts[0].strip())
                consequent = self._convert_formula(parts[1].strip())
                return f"(implies {antecedent} {consequent})"

        # Handle conjunction: p & q becomes (and p q)
        if '&' in formula:
            parts = [p.strip() for p in formula.split('&')]
            if len(parts) == 2:
                return f"(and {self._convert_formula(parts[0])} {self._convert_formula(parts[1])})"

        # Handle disjunction: p | q becomes (or p q)
        if '|' in formula:
            parts = [p.strip() for p in formula.split('|')]
            if len(parts) == 2:
                return f"(or {self._convert_formula(parts[0])} {self._convert_formula(parts[1])})"

        # Handle negation: ~p becomes (not p)
        if formula.startswith('~'):
            return f"(not {self._convert_formula(formula[1:].strip())})"

        # Atom (simple propositional variable)
        return formula

    def generate_metta(self) -> str:
        """Generate complete MeTTa file"""
        lines = []

        lines.append(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;")
        lines.append(";;; TPTP to MeTTa - Generated Backward Chainer Code")
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
            metta_formula = self._convert_formula(formula)
            lines.append(f";; {name}")
            lines.append(f"!(add-atom &kb {metta_formula})")
        lines.append("")

        # Rule Base
        lines.append(";;; Rule Base (Inference Rules)")
        lines.append("!(bind! &rb (new-space))")
        lines.append("")
        for name, formula in self.rb_rules:
            # Extract premise and conclusion from implication
            if '=>' in formula:
                parts = formula.split('=>')
                if len(parts) == 2:
                    premise = self._convert_formula(parts[0].strip())
                    conclusion = self._convert_formula(parts[1].strip())
                    lines.append(f";; {name}")
                    lines.append(f"!(add-atom &rb (⊢ {premise} {conclusion}))")
        lines.append("")

        # Backward Chainer
        lines.append(";;; Backward Chainer (Nil's pattern)")
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
            goal_metta = self._convert_formula(goal_formula)
            lines.append(";;; Query (Prove the conjecture)")
            lines.append(f"! \"=== Proving {goal_name} ===\"")
            lines.append(f"!(bc {goal_metta} (fromNumber 5))")
            lines.append("")
            lines.append(f";; Expected: {goal_metta}")

        return "\n".join(lines)

def main():
    """Convert simple_prop.p to MeTTa"""
    converter = TPTPToMeTTa()
    converter.parse_fof_file('simple_prop.p')
    metta_code = converter.generate_metta()

    # Write to file
    output_file = 'simple_prop.metta'
    with open(output_file, 'w') as f:
        f.write(metta_code)

    print(f"✅ Converted TPTP to MeTTa: {output_file}")
    print(f"   KB Facts: {len(converter.kb_facts)}")
    print(f"   RB Rules: {len(converter.rb_rules)}")
    print(f"   Goal: {converter.goal[0] if converter.goal else 'None'}")

if __name__ == '__main__':
    main()
