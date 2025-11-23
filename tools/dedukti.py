#!/usr/bin/env python3
"""
Dedukit: Translator from Vampire's Dedukti output (.dk) to Megalodon (.mg).
"""

import sys
import re
import os

# --- Lexer ---

TOKEN_SPEC = [
    ('ESCAPED',     r'\{\|.*?\|\}'),
    ('LPAREN',      r'\('),
    ('RPAREN',      r'\)') ,
    ('LBRACKET',    r'\[') ,
    ('RBRACKET',    r'\]') ,
    ('COLON_EQ',    r':=') ,
    ('COLON',       r':') ,
    ('DOT',         r'\.') ,
    ('ARROW_MAP',   r'=>') ,
    ('ARROW_TY',    r'->') ,
    ('ARROW_REW',   r'-->') ,
    ('ID',          r'[a-zA-Z0-9_]+') ,
    ('SKIP',        r'[ \t\n]+') ,
    ('MISC',        r'.') ,
]

class Lexer:
    def __init__(self, text):
        # Preprocess comments to simplify lexing
        # Block comments (; ... ;)
        text = re.sub(r'\(\;.*?\;\)', '', text, flags=re.DOTALL)
        # Line comments % ...
        text = re.sub(r'%[^\n]*', '', text)
        # Line comments # ...
        text = re.sub(r'#[^\n]*', '', text)
        
        self.regex = '|'.join('(?P<%s>%s)' % pair for pair in TOKEN_SPEC)
        self.text = text
        self.pos = 0
        self.len = len(text)
    
    def __iter__(self):
        regex = re.compile(self.regex) # No DOTALL needed for tokens
        while self.pos < self.len:
            match = regex.match(self.text, self.pos)
            if match:
                kind = match.lastgroup
                value = match.group(kind)
                self.pos = match.end()
                if kind == 'SKIP':
                    continue
                yield kind, value
            else:
                raise RuntimeError(f"Unexpected character at pos {self.pos}: {self.text[self.pos]}")
        yield 'EOF', ''

# --- Parser ---

class Parser:
    def __init__(self, tokens):
        self.tokens = list(tokens)
        self.pos = 0
    
    def peek(self):
        if self.pos >= len(self.tokens):
            return ('EOF', '')
        return self.tokens[self.pos]
    
    def consume(self, kind=None):
        k, v = self.tokens[self.pos]
        if kind and k != kind:
            raise RuntimeError(f"Expected {kind}, got {k} ('{v}') at token pos {self.pos}")
        self.pos += 1
        return k, v
    
    def parse_file(self):
        items = []
        while self.peek()[0] != 'EOF':
            items.append(self.parse_item())
        return items

    def parse_item(self):
        # Items can be:
        # ID : Type. (Declaration)
        # def ID : Type := Term. (Definition)
        # [ ... ] ... --> ... (Rewrite rule - ignore or store) 
        
        k, v = self.peek()
        if k == 'LBRACKET':
            # Rewrite rule
            return self.parse_rewrite()
        elif k == 'ID' or k == 'ESCAPED':
            # Decl or Def
            name = v
            self.consume() # Name or 'def'
            
            # Skip TPTP-style cnf(...) lines that may appear in dk output comments
            if name == 'cnf':
                # consume until dot
                while self.peek()[0] != 'DOT' and self.peek()[0] != 'EOF':
                    self.consume()
                if self.peek()[0] == 'DOT':
                    self.consume('DOT')
                return ('REWRITE',)
            
            if name == 'def' or name == 'injective':
                # It is a definition or modifier
                name_k, name_v = self.consume() # Real Name
                if name_k not in ('ID', 'ESCAPED'):
                     raise RuntimeError(f"Expected ID after {name}, got {name_k} ({name_v})")
                name = name_v
                # Continue as usual expecting :
            
            if self.peek()[0] == 'COLON':
                self.consume('COLON')
                typ = self.parse_term()
                if self.peek()[0] == 'COLON_EQ':
                    self.consume('COLON_EQ')
                    term = self.parse_term()
                    self.consume('DOT')
                    return ('DEF', name, typ, term)
                else:
                    self.consume('DOT')
                    return ('DECL', name, typ)
            else:
                raise RuntimeError(f"Expected : after {name}, got {self.peek()}")
        else:
            raise RuntimeError(f"Unexpected token at top level: {k} ({v}) at token pos {self.pos}")

    def parse_rewrite(self):
        # [ ... ] LHS --> RHS.
        while self.peek()[0] != 'DOT' and self.peek()[0] != 'EOF':
            self.consume()
        self.consume('DOT')
        return ('REWRITE',)

    def parse_term(self):
        # Check for Binder: ID : ...
        is_binder = False
        if self.peek()[0] in ('ID', 'ESCAPED'):
             if self.pos + 1 < len(self.tokens) and self.tokens[self.pos+1][0] == 'COLON':
                 is_binder = True
        
        if is_binder:
            var = self.consume()[1] # var
            self.consume('COLON')
            ty = self.parse_term()
            
            k, v = self.peek()
            if k == 'ARROW_TY':
                 self.consume()
                 body = self.parse_term()
                 return ('PI', var, ty, body)
            elif k == 'ARROW_MAP':
                 self.consume()
                 body = self.parse_term()
                 return ('LAMBDA', var, ty, body)
            else:
                 # Just typed term (e.g. inside parens)
                 return ('TYPED', var, ty)

        # Simple recursive descent for terms
        
        parts = []
        while True:
            k, v = self.peek()
            if k in ('DOT', 'RPAREN', 'RBRACKET', 'EOF', 'COLON_EQ', 'ARROW_MAP'):
                break
            
            if k == 'LPAREN':
                self.consume()
                t = self.parse_term()
                self.consume('RPAREN')
                parts.append(t)
            
            elif k == 'ARROW_TY':
                break
            elif k in ('ID', 'ESCAPED'):
                self.consume()
                parts.append(('VAR', v))
            else:
                break
        
        if not parts:
            raise RuntimeError(f"Empty term at {self.peek()}")
            
        # Construct application (left associative)
        term = parts[0]
        for p in parts[1:]:
            term = ('APP', term, p)
            
        # Handle trailing arrows (Pi/Lambda that wasn't parenthesized?)
        # Dedukti: A -> B
        k, v = self.peek()
        if k == 'ARROW_TY':
            self.consume()
            rhs = self.parse_term()
            # A -> B is Pi _ : A -> B
            term = ('ARROW', term, rhs)

        return term

# --- Translator ---

class Translator:
    def __init__(self):
        self.out = []
        self.mapping = {
            'Prop': 'prop',
            'Type': 'type', # or set?
            'Set': 'set',
            'true': 'True',
            'false': 'False',
            'not': 'not',
            'and': 'and',
            'or': 'or',
            'imp': 'imp',
            'iff': 'iff',
            'forall': 'forall', 'forall_': 'forall',
            'exists': 'exists', 'exists_': 'exists',
            'eq': 'eq',
            'refl': 'eqI', # ?
            'iota': 'set',
            'cand': 'and',
            'cor': 'or',
            'cimp': 'imp',
            'if': 'av_if',
            'prop_clause': 'dk_prop_clause',
            'clause': 'dk_clause',
            'av_clause': 'dk_av_clause',
            'cons': 'dk_cons',
            'cl': 'dk_cl',
            'ec': 'dk_ec',
            'acl': 'dk_acl',
        }
        self.vars = {}
    
    def sanitize(self, name):
        if name.startswith('{|') and name.endswith('|}'):
            name = name[2:-2]
        # Replace invalid chars
        name = name.replace('.', '_').replace('-', '_')
        # Ensure not keyword
        if name in ['fun', 'forall', 'exists', 'let', 'in', 'match', 'with']:
            name = name + '_'
        
        # Avoid leading non-letters by prefixing with x (prevents clashes with true identifiers like v0)
        if not name[0].isalpha() and name[0] != '_':
            return f"x{name}"
            
        return name

    def translate_term(self, term, env=None):
        if env is None:
            env = {}
        kind = term[0]
        if kind == 'VAR':
            name = self.sanitize(term[1])
            mapped = env.get(term[1], name)
            return self.mapping.get(mapped, mapped)
        elif kind == 'APP':
            # Flatten app
            args = []
            curr = term
            while curr[0] == 'APP':
                args.append(curr[2])
                curr = curr[1]
            args.append(curr) # This is the head
            head = args.pop()
            args.reverse() 
            
            head_str = self.translate_term(head, env)
            
            # Handle special forms
            if head_str == 'El':
                return 'set'
            
            if head_str == 'eq':
                if len(args) == 3:
                    lhs = self.translate_term(args[1], env)
                    rhs = self.translate_term(args[2], env)
                    return f"({lhs} = {rhs})"
            
            if head_str == 'imp':
                if len(args) == 2:
                    lhs = self.translate_term(args[0], env)
                    rhs = self.translate_term(args[1], env)
                    return f"({lhs} -> {rhs})"
            
            if head_str == 'comm' and len(args) >= 4:
                arg_strs = [self.translate_term(a, env) for a in args]
                if arg_strs and arg_strs[0] == 'set':
                    arg_strs = arg_strs[1:]
                return f"(comm {' '.join(arg_strs)})"
            
            if head_str == 'comml' and len(args) >= 3:
                arg_strs = [self.translate_term(a, env) for a in args]
                if arg_strs and arg_strs[0] == 'set':
                    arg_strs = arg_strs[1:]
                return f"(comml {' '.join(arg_strs)})"

            if head_str == 'eqI' or head_str == 'refl':
                if len(args) == 2:
                    # Drop the type argument (first)
                    return f"(eqI {self.translate_term(args[1], env)})"
                if len(args) == 1:
                    return f"(eqI {self.translate_term(args[0], env)})"
            
            if head_str == 'Prf':
                return self.translate_term(args[0], env)
            if head_str == 'Prf_clause':
                return self.translate_clause(args[0], env)
            if head_str == 'Prf_prop_clause':
                return self.translate_prop_clause(args[0], env)
            
            if head_str == 'bind':
                if len(args) == 2:
                    domain = self.translate_term(args[0], env)
                    func = args[1]
                    if func[0] == 'LAMBDA':
                        var_raw = func[1]
                        var = self.sanitize(var_raw)
                        env2 = env.copy()
                        env2[var_raw] = var
                        body = self.translate_clause(func[3], env2)
                        return f"(forall {var} : {domain}, {body})"
            
            if head_str == 'bind_poly':
                if len(args) == 1:
                    func = args[0]
                    if func[0] == 'LAMBDA':
                        var_raw = func[1]
                        var = self.sanitize(var_raw)
                        env2 = env.copy()
                        env2[var_raw] = var
                        body = self.translate_clause(func[3], env2)
                        return f"(forall {var} : set, {body})" # set? bind_poly quantifies over types?
            
            if head_str == 'forall_poly':
                if len(args) == 1:
                    pred = args[0]
                    if pred[0] == 'LAMBDA':
                        var_raw = pred[1]
                        var = self.sanitize(var_raw)
                        env2 = env.copy()
                        env2[var_raw] = var
                        body = self.translate_term(pred[3], env2)
                        return f"(forall {var} : set, {body})"

            if head_str == 'cPrf':
                return f"(dk_cPrf {self.translate_clause(args[0], env)})"

            if head_str in ['forall', 'exists', 'forall_', 'exists_', 'cforall', 'cexists']:
                if len(args) == 2:
                    domain = self.translate_term(args[0], env)
                    pred = args[1]
                    if pred[0] == 'LAMBDA':
                        var_raw = pred[1]
                        var = self.sanitize(var_raw)
                        env2 = env.copy()
                        env2[var_raw] = var
                        body = self.translate_term(pred[3], env2)
                        return f"({head_str} {var} : {domain}, {body})"
                    else:
                        return f"({head_str} {self.translate_term(pred, env)})"
            
            arg_strs = [self.translate_term(a, env) for a in args]
            return f"({head_str} {' '.join(arg_strs)})"

        elif kind == 'MAP':
            lhs = term[1]
            rhs_str = self.translate_term(term[2], env)
            if lhs[0] == 'TYPED':
                var_raw = lhs[1]
                var = self.sanitize(var_raw)
                env2 = env.copy()
                env2[var_raw] = var
                ty = self.translate_term(lhs[2], env)
                return f"(fun {var} : {ty} => {self.translate_term(term[2], env2)})"
            lhs_str = self.translate_term(lhs, env)
            return f"(fun {lhs_str} => {rhs_str})"

        elif kind == 'LAMBDA':
            var_raw = term[1]
            var = self.sanitize(var_raw)
            env2 = env.copy()
            env2[var_raw] = var
            ty = self.translate_term(term[2], env)
            body = self.translate_term(term[3], env2)
            return f"(fun {var} : {ty} => {body})"
        
        elif kind == 'PI':
            var_raw = term[1]
            var = self.sanitize(var_raw)
            env2 = env.copy()
            env2[var_raw] = var
            ty = self.translate_term(term[2], env)
            body = self.translate_term(term[3], env2)
            return f"(forall {var} : {ty}, {body})"
        
        elif kind == 'ARROW':
            lhs = term[1]
            rhs_str = self.translate_term(term[2], env)
            
            if lhs[0] == 'TYPED':
                var_raw = lhs[1]
                var = self.sanitize(var_raw)
                env2 = env.copy()
                env2[var_raw] = var
                ty = self.translate_term(lhs[2], env)
                return f"(forall {var} : {ty}, {self.translate_term(term[2], env2)})"
            
            lhs_str = self.translate_term(lhs, env)
            return f"({lhs_str} -> {rhs_str})"
            
        elif kind == 'TYPED':
             return f"({self.sanitize(term[1])} : {self.translate_term(term[2], env)})"
            
        else:
            return f"UNKNOWN_TERM_{kind}"

    def translate_clause(self, term, env=None):
        if env is None:
            env = {}
        if term[0] == 'APP':
            head = term[1]
            if head[0] == 'VAR' and head[1] == 'cl':
                return self.translate_prop_clause(term[2], env)
        return self.translate_prop_clause(term, env)

    def translate_prop_clause(self, term, env=None):
        if env is None:
            env = {}
        lits = []
        curr = term
        while True:
            if curr[0] == 'APP':
                fun = curr[1]
                if fun[0] == 'APP':
                    f = fun[1]
                    if f[0] == 'VAR' and f[1] == 'cons':
                        p = fun[2]
                        c = curr[2]
                        lits.append(p)
                        curr = c
                        continue
            if curr[0] == 'VAR' and curr[1] == 'ec':
                break
            # Not a recognized clause structure; fall back.
            return self.translate_term(term, env)

        # Build dk_cons chain in the same (left-to-right) order as the Dedukti prelude.
        res = "dk_ec"
        for p in reversed(lits):
            p_str = self.translate_term(p, env)
            res = f"(dk_cons {p_str} {res})"
        return res

    def is_proof_type(self, t):
        curr = t
        while True:
            if curr[0] == 'PI':
                curr = curr[3]
            elif curr[0] == 'ARROW':
                curr = curr[2]
            elif curr[0] == 'APP':
                head = curr[1]
                while head[0] == 'APP':
                    head = head[1]
                if head[0] == 'VAR':
                    if head[1] in ['Prf', 'Prf_clause', 'Prf_prop_clause', 'Prf_av_clause', 'cPrf']:
                        return True
                return False
            else:
                return False

    def process(self, items):
        self.out.append("Section DeduktiProof.")
        
        SKIP_NAMES = {
            'Prop', 'Type', 'Set', 'Prf', 'true', 'false', 'not', 'and', 'or', 'imp', 'iff', 
            'forall', 'exists', 'eq', 'refl', 'comm', 'comml', 'comml_not',
            'El', 'iota', 'inhabit',
            'prop_clause', 'ec', 'cons', 'clause', 'cl', 'bind', 'bind_poly',
            'Prf_prop_clause', 'Prf_clause',
            'av_clause', 'acl', 'if', 'Prf_av_clause',
            'forall_poly', 'cPrf', 'cand', 'cor', 'cimp', 'cforall', 'cexists'
        }
        
        for item in items:
            kind = item[0]
            if kind == 'REWRITE':
                continue
            if kind == 'DECL':
                raw_name = item[1]
                if raw_name in SKIP_NAMES:
                    continue
                    
                name = self.sanitize(raw_name)
                
                is_proof = self.is_proof_type(item[2])
                
                ty = self.translate_term(item[2])
                
                if is_proof:
                    self.out.append(f"Hypothesis {name} : {ty}.")
                else:
                    self.out.append(f"Variable {name} : {ty}.")
                    
            elif kind == 'DEF':
                raw_name = item[1]
                if raw_name in SKIP_NAMES:
                    continue

                name = self.sanitize(raw_name)
                
                is_proof = self.is_proof_type(item[2])
                
                ty = self.translate_term(item[2])
                tm = self.translate_term(item[3])
                
                if is_proof:
                    self.out.append(f"Theorem {name} : {ty}.")
                    self.out.append(f"exact {tm}.")
                    self.out.append("Qed.")
                else:
                    self.out.append(f"Definition {name} : {ty} := {tm}.")
        
        self.out.append("End DeduktiProof.")

    def get_output(self):
        return "\n".join(self.out)

def main():
    if len(sys.argv) < 2:
        print("Usage: dedukti.py <file.dk>")
        sys.exit(1)
        
    with open(sys.argv[1], 'r') as f:
        text = f.read()
        
    lexer = Lexer(text)
    parser = Parser(lexer)
    items = parser.parse_file()
    
    trans = Translator()
    trans.process(items)
    
    print(trans.get_output())

if __name__ == "__main__":
    main()
