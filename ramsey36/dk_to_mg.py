#!/usr/bin/env python3
"""
Minimal Dedukti (.dk) -> Megalodon (.mg) translator scaffold.

This is intentionally small and focused on the FOL fragments emitted by
Vampire's `-p dedukti --proof_extra full`. It currently:
  - Tokenises the .dk file
  - Builds a bare-bones AST for terms (variables, applications, lambdas, arrows)
  - Records constant declarations (`name : type.`) and definitions (`def name : type := term.`)
  - Prints a summary of the final constants so we can iteratively extend the
    translator to emit Megalodon.

Next steps (not yet implemented here):
  - Implement a real term-to-term translation into Megalodon syntax
  - Reconstruct the axiom context for the TPTP problem
  - Emit a full .mg file with the translated proof term for `Prf false`
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict, Union, Iterator

Token = Tuple[str, str]  # (kind, value)


def tokenize(src: str) -> List[Token]:
    """
    Very small tokenizer for Dedukti. It recognises:
      - parentheses (), brackets [], braces {} (as individual symbols)
      - arrows '->' and rewrite arrows '-->'
      - binders ':' and ':=' and '=>'
      - identifiers (including {|foo|} style)
      - dots '.'
    Comments (% …) should be stripped by caller.
    """
    tokens: List[Token] = []
    i = 0
    while i < len(src):
        c = src[i]
        if c.isspace():
            i += 1
            continue
        if src.startswith("-->", i):
            tokens.append(("ARROW_REWRITE", "-->"))
            i += 3
            continue
        if src.startswith("->", i):
            tokens.append(("ARROW", "->"))
            i += 2
            continue
        if src.startswith(":=", i):
            tokens.append(("DEF", ":="))
            i += 2
            continue
        if src.startswith("=>", i):
            tokens.append(("LAMBDA", "=>"))
            i += 2
            continue
        if c in "().[]{}":
            tokens.append((c, c))
            i += 1
            continue
        if c == ":":
            tokens.append(("COLON", ":"))
            i += 1
            continue
        if c == ".":
            tokens.append(("DOT", "."))
            i += 1
            continue
        # identifiers, including {|name|}
        if c == "{":
            m = re.match(r"\{\|[^|]+\|\}", src[i:])
            if not m:
                raise ValueError(f"Bad quoted identifier near {src[i:i+20]}")
            val = m.group(0)
            tokens.append(("ID", val))
            i += len(val)
            continue
        m = re.match(r"[A-Za-z0-9_]+", src[i:])
        if m:
            val = m.group(0)
            tokens.append(("ID", val))
            i += len(val)
            continue
        raise ValueError(f"Unexpected char {c!r} at {i}")
    return tokens


# AST nodes
@dataclass
class Term:
    pass


@dataclass
class Var(Term):
    name: str


@dataclass
class App(Term):
    fn: Term
    arg: Term


@dataclass
class Lam(Term):
    var: str
    type: Optional[Term]  # may be None for unannotated lambda
    body: Term


@dataclass
class Arrow(Term):
    dom: Term
    cod: Term


@dataclass
class ConstDecl:
    name: str
    type: Term


@dataclass
class ConstDef:
    name: str
    type: Term
    body: Term


class Parser:
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Optional[Token]:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def eat(self, kind: str) -> Token:
        tok = self.peek()
        if tok is None or tok[0] != kind:
            raise ValueError(f"Expected {kind} at {self.pos}, got {tok}")
        self.pos += 1
        return tok

    def parse_term(self) -> Term:
        """
        Parse arrow terms right-associatively: A -> B -> C  = A -> (B -> C).
        Applications are left-associative.
        Lambdas use [x] t or [x:T] t syntax (appearing in the dk prelude), but
        we also support explicit 'x : T => t' sugar.
        """
        term = self.parse_app()
        tok = self.peek()
        if tok and tok[0] in ("ARROW", "ARROW_REWRITE"):
            self.eat(tok[0])
            cod = self.parse_term()
            return Arrow(term, cod)
        return term

    def parse_app(self) -> Term:
        parts: List[Term] = []
        while True:
            tok = self.peek()
            if tok is None:
                break
            if tok[0] == "ID":
                parts.append(Var(tok[1]))
                self.pos += 1
            elif tok[0] == "(":
                self.eat("(")
                parts.append(self.parse_term())
                self.eat(")")
            elif tok[0] == "[":
                # lambda binder in dk: [x, y] body  or [x] body
                self.eat("[")
                binders: List[str] = []
                while True:
                    tok2 = self.peek()
                    if tok2 is None:
                        raise ValueError("Unclosed lambda binder")
                    if tok2[0] == "ID":
                        binders.append(tok2[1])
                        self.pos += 1
                        if self.peek() and self.peek()[0] == ",":
                            self.pos += 1
                            continue
                    elif tok2[0] == "]":
                        self.pos += 1
                        break
                    else:
                        raise ValueError(f"Unexpected token in binder {tok2}")
                body = self.parse_term()
                t: Term = body
                for b in reversed(binders):
                    t = Lam(b, None, t)
                parts.append(t)
            elif tok[0] == "LAMBDA":
                # explicit x : T => body
                self.eat("LAMBDA")
                if self.peek() and self.peek()[0] == "ID":
                    var = self.eat("ID")[1]
                    typ = None
                    if self.peek() and self.peek()[0] == "COLON":
                        self.eat("COLON")
                        typ = self.parse_term()
                    self.eat("ARROW") if self.peek() and self.peek()[0] == "ARROW" else None
                    body = self.parse_term()
                    parts.append(Lam(var, typ, body))
                else:
                    raise ValueError("Lambda expects an identifier")
            else:
                break
        if not parts:
            raise ValueError(f"Expected term at {self.pos}")
        term: Term = parts[0]
        for p in parts[1:]:
            term = App(term, p)
        return term

    def parse_decl_or_def(self) -> Union[ConstDecl, ConstDef]:
        tok = self.peek()
        if tok and tok[0] == "ID" and tok[1] == "def":
            self.eat("ID")  # def
            name = self.eat("ID")[1]
            self.eat("COLON")
            typ = self.parse_term()
            self.eat("DEF")  # :=
            body = self.parse_term()
            self.eat("DOT")
            return ConstDef(name, typ, body)
        elif tok and tok[0] == "ID":
            name = self.eat("ID")[1]
            self.eat("COLON")
            typ = self.parse_term()
            self.eat("DOT")
            return ConstDecl(name, typ)
        else:
            raise ValueError(f"Expected declaration/definition at {self.pos}")


def strip_comments(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if not line.strip().startswith("%"))


def main(path: str) -> None:
    src = strip_comments(open(path).read())
    toks = tokenize(src)
    p = Parser(toks)
    decls: Dict[str, ConstDecl] = {}
    defs: Dict[str, ConstDef] = {}
    while p.peek() is not None:
        try:
            item = p.parse_decl_or_def()
        except Exception as e:
            sys.stderr.write(f"Parse error at token {p.pos}: {e}\n")
            break
        if isinstance(item, ConstDecl):
            decls[item.name] = item
        else:
            defs[item.name] = item
    print(f"Parsed {len(decls)} declarations, {len(defs)} definitions.")
    if "false" in decls:
        print("Found primitive false.")
    # Try to find a definition with type `Prf false`
    targets = [d for d in defs.values() if isinstance(d.type, App) and isinstance(d.type.fn, Var) and d.type.fn.name == "Prf" and isinstance(d.type.arg, Var) and d.type.arg.name == "false"]
    print(f"Found {len(targets)} defs of type Prf false.")
    if targets:
        print("Example target name:", targets[-1].name)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} path/to/file.dk")
        sys.exit(1)
    main(sys.argv[1])
