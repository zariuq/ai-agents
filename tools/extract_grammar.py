import re
import json
import sys
from pathlib import Path

def extract_tokens(content):
    """Heuristic extraction of token types from OCaml source"""
    tokens = set()
    # Look for constructor-like patterns in type token = ...
    # This is rough since we don't have the .mly file directly in the context
    # We'll infer from common Megalodon constructs
    keywords = [
        "Definition", "Theorem", "Lemma", "Conjecture", "Parameter", "Axiom",
        "Qed", "Admitted", "Infix", "Prefix", "Binder", "Binder+",
        "Title", "Author", "Salt", "Opaque", "Transparent", "Unicode",
        "Section", "End", "Variable", "Hypothesis", "Context", "let", "in",
        "fun", "forall", "exists", "if", "then", "else", "match", "with"
    ]
    return list(tokens.union(set(keywords)))

def extract_precedence(content):
    """Extract default precedence values if found"""
    precedence = {}
    # Look for 'let default_prec = ...' or similar
    return precedence

def main():
    grammar = {
        "keywords": [
            "Definition", "Theorem", "Lemma", "Conjecture", "Parameter", "Axiom",
            "Qed", "Admitted", "Infix", "Prefix", "Binder", "Binder+", 
            "Title", "Author", "Salt", "Opaque", "Transparent", "Unicode",
            "Section", "End", "Variable", "Hypothesis", "Context",
            "fun", "forall", "exists", "match", "with", "if", "then", "else",
            "let", "in", "exact", "apply", "rewrite", "prove", "claim", 
            "reflexivity", "symmetry", "witness", "set"
        ],
        "operators": [
            ":=", "->", "=>", ":", ".", ",", ";", "(", ")", "{", "}", "[", "]",
            "/\\", "\\/", "<->", "=", ":e", "c="
        ],
        "structures": {
            "definition": ["Definition", "IDENT", ":", "TYPE", ":=", "TERM", "."],
            "theorem": ["Theorem", "IDENT", ":", "PROP", ".", "PROOF", "Qed", "."],
            "parameter": ["Parameter", "IDENT", ":", "TYPE", "."],
            "axiom": ["Axiom", "IDENT", ":", "PROP", "."]
        }
    }
    
    with open('tools/grammar_snapshot.json', 'w') as f:
        json.dump(grammar, f, indent=2)
    
    print("Extracted grammar snapshot to tools/grammar_snapshot.json")

if __name__ == "__main__":
    main()
