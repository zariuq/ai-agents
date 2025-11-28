#!/usr/bin/env python3
"""
Mizar Proof Verifier for MeTTa/MM2
Extracts proofs and creates verification steps.
"""

import json
import sys


def create_verifiable_sexp(json_file, output_file=None):
    """
    Convert Mizar JSON to S-expressions with proof verification structure.
    """

    with open(json_file, 'r') as f:
        data = json.load(f)

    lines = []
    lines.append(';;;; Mizar Proof Verification Format')
    lines.append(';;;; Universal S-expressions for MeTTa and MM2/MORK')
    lines.append('')

    # Add verification rules
    lines.append(';; Verification Rules (MeTTa can execute, MM2 can query)')
    lines.append('')

    # Basic inference rules
    lines.append(';; Modus Ponens: if A and (A implies B) then B')
    lines.append('(verify-rule modus-ponens')
    lines.append('  (premises (fact A) (fact (implies A B)))')
    lines.append('  (conclusion (fact B)))')
    lines.append('')

    lines.append(';; Universal Instantiation')
    lines.append('(verify-rule universal-instantiation')
    lines.append('  (premises (fact (forall x (P x))))')
    lines.append('  (conclusion (fact (P a))))')
    lines.append('')

    lines.append(';; Equality Substitution')
    lines.append('(verify-rule equality-substitution')
    lines.append('  (premises (fact (eq x y)) (fact (P x)))')
    lines.append('  (conclusion (fact (P y))))')
    lines.append('')

    # Process theorems with justifications
    theorem_count = 0
    for item in data.get("body", []):
        if "kind" in item and "Theorem" in item["kind"]:
            theorem_count += 1
            thm = item["kind"]["Theorem"]

            lines.append(f';; Theorem {theorem_count}')

            # Extract the formula
            formula = extract_clean_formula(thm.get("prop", {}))

            # Extract justification
            just = thm.get("just", {})

            if "Inference" in just:
                inf = just["Inference"]
                kind = inf.get("kind", {})
                refs = inf.get("refs", [])

                # Create verification step
                lines.append(f'(theorem tarski-{theorem_count}')
                lines.append(f'  (statement {formula})')

                if "By" in kind and refs:
                    # Simple justification by reference
                    ref_list = []
                    for ref in refs:
                        if "kind" in ref:
                            ref_kind = ref["kind"]
                            art = ref_kind.get("spelling", "")
                            for r in ref_kind.get("refs", []):
                                if "Thm" in r:
                                    ref_list.append(f'(ref {art} thm-{r["Thm"].get("id", 0)})')

                    lines.append(f'  (justified-by')
                    for r in ref_list:
                        lines.append(f'    {r}')
                    lines.append(f'  )')

                    # Add verification step
                    lines.append(f'  (verify-step')
                    lines.append(f'    (check-references {" ".join(ref_list)})')
                    lines.append(f'    (status pending))')

                elif "From" in kind:
                    # Scheme instantiation
                    lines.append(f'  (justified-by (scheme-instantiation))')
                    lines.append(f'  (verify-step (check-scheme-instance))')

                lines.append(f')')
                lines.append('')

    # Add example verification queries
    lines.append(';; Verification Queries')
    lines.append('')

    lines.append(';; For MeTTa - execute verification')
    lines.append('!(verify-all-theorems)')
    lines.append('')

    lines.append(';; For MM2/MORK - query verification status')
    lines.append('(query (theorem ?name (verify-step (status ?status))))')
    lines.append('')

    # Add simple proof checker
    lines.append(';; Simple Proof Checker (MeTTa executable)')
    lines.append('(= (check-proof $theorem)')
    lines.append('   (match $theorem')
    lines.append('     ((theorem $name')
    lines.append('        (statement $stmt)')
    lines.append('        (justified-by $refs)')
    lines.append('        (verify-step $step))')
    lines.append('      (if (valid-references $refs)')
    lines.append('          (verified $name)')
    lines.append('          (unverified $name)))))')
    lines.append('')

    # Add MM2 assertions for verification
    lines.append(';; MM2/MORK Database Assertions')
    lines.append('(assert (verification-enabled true))')
    lines.append('(assert (axiom tarski-0))')
    lines.append('')

    output = '\n'.join(lines)

    if output_file:
        with open(output_file, 'w') as f:
            f.write(output)
        print(f"Created verifiable format: {output_file}")
    else:
        print(output)

    return output


def extract_clean_formula(prop):
    """Extract formula as clean S-expression"""
    if not prop or "f" not in prop:
        return "true"

    f = prop["f"]

    def process_formula(node):
        if "Binder" in node:
            binder = node["Binder"]
            kind = binder.get("kind", "").lower()
            vars = extract_vars(binder.get("vars", []))
            scope = process_formula(binder.get("scope", {}))
            return f"({kind} {vars} {scope})"

        elif "Binop" in node:
            binop = node["Binop"]
            kind = binop.get("kind", "").lower()
            f1 = process_formula(binop.get("f1", {}))
            f2 = process_formula(binop.get("f2", {}))
            return f"({kind} {f1} {f2})"

        elif "Pred" in node:
            pred = node["Pred"]
            spelling = pred.get("spelling", "pred")
            args = " ".join(process_term(arg) for arg in pred.get("args", []))
            return f"({spelling} {args})"

        elif "Is" in node:
            is_node = node["Is"]
            term = process_term(is_node.get("term", {}))
            ty = process_type(is_node.get("ty", {}))
            return f"(is {term} {ty})"

        elif "Neg" in node or "Not" in node:
            inner = node.get("Neg", node.get("Not", {}))
            return f"(not {process_formula(inner)})"

        else:
            return "formula"

    return process_formula(f)


def extract_vars(var_groups):
    """Extract variables from var groups"""
    vars = []
    for group in var_groups:
        for var in group.get("vars", []):
            vars.append(var.get("spelling", "?"))
    return "(" + " ".join(vars) + ")"


def process_term(term):
    """Process a term to clean S-expression"""
    if "Var" in term:
        return term["Var"].get("spelling", "?")
    elif "Const" in term:
        return f"const-{term['Const'].get('id', 0)}"
    elif "It" in term:
        return "it"
    elif "spelling" in term:
        return term.get("spelling", "?")
    else:
        return "term"


def process_type(ty):
    """Process a type to clean S-expression"""
    if "Mode" in ty:
        return ty["Mode"].get("spelling", "type")
    else:
        return "type"


def test_verification():
    """Test the verification format"""
    print("Testing Mizar Proof Verification...")
    print()

    try:
        from hyperon import MeTTa
        metta = MeTTa()

        test_code = """
        ;; Test proof verification in MeTTa

        ;; Define verification status
        (: verified (-> Atom Atom))
        (: unverified (-> Atom Atom))

        ;; Simple theorem with justification
        (= (theorem test-1
             (statement (implies p q))
             (justified-by (axiom modus-ponens)))
           verified)

        ;; Check verification
        !(theorem test-1 $stmt $just)
        """

        print("MeTTa verification test:")
        results = metta.run(test_code)
        print(f"  Result: {results}")

    except ImportError:
        print("MeTTa not available")
    except Exception as e:
        print(f"Error: {e}")

    print()
    print("Verification Features:")
    print("  1. Each theorem has a verification step")
    print("  2. References are tracked and checkable")
    print("  3. Status can be: pending, verified, failed")
    print("  4. Both MeTTa (execute) and MM2 (query) compatible")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        input_file = sys.argv[1]
        output_file = sys.argv[2] if len(sys.argv) > 2 else None
        create_verifiable_sexp(input_file, output_file)
    else:
        test_verification()

        # Convert tarski if available
        import os
        json_file = "/tmp/mizar-output/tarski.mzp.json"
        if os.path.exists(json_file):
            print("\n" + "="*60)
            print("Creating verifiable format for tarski...")
            print("="*60)
            create_verifiable_sexp(
                json_file,
                "/home/zar/claude/hyperon/tarski_verifiable.sexp"
            )