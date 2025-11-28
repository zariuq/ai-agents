import sys
import re

DEFAULT_INFIX = {'->': (800, 'right')}
DEFAULT_PREFIX = {}

def tokenize(text):
    # 1. Remove comments (* ... *)
    # Non-nested comments: \(\*.*?\*\)
    # Use DOTALL to match across newlines
    text = re.sub(r'\(\*.*?\*\)', ' ', text, flags=re.DOTALL)
    
    # 2. Split by whitespace and special chars/operators
    pattern = r'(\s+|:=|->|=>|[\(\)\:\.\,\{\}\[\]])'
    parts = re.split(pattern, text)
    
    # Filter out empty strings and whitespace
    tokens = [p for p in parts if p and not p.strip() == '']
    return tokens

class MGParser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0
        self.infix_ops = dict(DEFAULT_INFIX)
        self.prefix_ops = dict(DEFAULT_PREFIX)

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected=None):
        if self.pos >= len(self.tokens):
            raise Exception("Unexpected EOF")
        token = self.tokens[self.pos]
        if expected and token != expected:
            raise Exception(f"Expected '{expected}', got '{token}' at position {self.pos}")
        self.pos += 1
        return token

    def parse_file(self):
        exprs = []
        while self.pos < len(self.tokens):
            token = self.peek()
            if token == 'Definition':
                exprs.append(self.parse_definition())
            elif token == 'Theorem' or token == 'Lemma' or token == 'Conjecture':
                exprs.append(self.parse_theorem())
            elif token == 'Parameter':
                exprs.append(self.parse_parameter())
            elif token == 'Variable':
                exprs.append(self.parse_variable())
            elif token == 'Axiom':
                exprs.append(self.parse_axiom())
            elif token == 'Section':
                self.consume('Section')
                name = self.consume()
                self.consume('.')
                exprs.append(['Section', name])
            elif token == 'End':
                self.consume('End')
                name = self.consume()
                self.consume('.')
                exprs.append(['End', name])
            elif token in ['Infix', 'Prefix', 'Binder', 'Binder+', 'Title', 'Author', 'Salt', 'Opaque', 'Transparent', 'Unicode']:
                exprs.append(self.parse_declaration())
            elif token == 'Qed' or token == '.' or token == 'Admitted': 
                self.consume()
            else:
                # Skip unknown token
                # print(f"Warning: Skipping unexpected token '{token}' at top level")
                self.consume()
        return exprs

    def parse_declaration(self):
        cmd = self.consume()
        args = []
        while self.peek() != '.':
            args.append(self.consume())
        self.consume('.')

        if cmd == 'Infix':
            # Format: Infix op [op_parts...] prec [assoc] := def
            # Scan for precedence (first int)
            prec_idx = -1
            for i, arg in enumerate(args):
                if arg.isdigit():
                    prec_idx = i
                    break
            
            if prec_idx != -1:
                # Reconstruct operator from parts before prec
                op = "".join(args[:prec_idx])
                prec = int(args[prec_idx])
                
                # Check associativity
                assoc = 'none'
                if prec_idx + 1 < len(args):
                    next_tok = args[prec_idx + 1]
                    if next_tok in ['left', 'right', 'none']:
                        assoc = next_tok
                
                self.infix_ops[op] = (prec, assoc)
                # Store simplified version for metta output? 
                # We return the original args, but maybe we should normalize the op in the args?
                # For round-tripping, it's better to keep the AST clean. 
                # Let's modify the returned args to combine the operator tokens
                return [cmd, op, str(prec), assoc, ':=', args[-1]] 
                # Wait, args might contain 'left' or ':='.
                # Let's just return [cmd] + args, the important part is updating self.infix_ops for PARSING.
                # The AST passed to metta doesn't strictly need the operator to be a single string, 
                # BUT metta_to_mg expects (Infix op prec assoc ...).
                # So yes, let's normalize the return structure.
                
                # Find def: look for :=
                def_val = args[-1] # Default
                if ':=' in args:
                    def_val = args[args.index(':=') + 1]
                
                return [cmd, op, str(prec), assoc, ':=', def_val]

        if cmd == 'Prefix':
            # Prefix op prec := def
            prec_idx = -1
            for i, arg in enumerate(args):
                if arg.isdigit():
                    prec_idx = i
                    break
            
            if prec_idx != -1:
                op = "".join(args[:prec_idx])
                prec = int(args[prec_idx])
                self.prefix_ops[op] = prec
                
                def_val = args[-1]
                if ':=' in args:
                    def_val = args[args.index(':=') + 1]
                return [cmd, op, str(prec), ':=', def_val]

        return [cmd] + args

    def parse_definition(self):
        self.consume('Definition')
        name = self.consume()
        self.consume(':')
        
        # Type
        type_tokens = []
        while self.peek() != ':=':
            type_tokens.append(self.consume())
        
        self.consume(':=')
        
        # Body
        body_tokens = []
        while self.peek() != '.':
            body_tokens.append(self.consume())
        self.consume('.')

        return ['Definition', name, self.convert_term(type_tokens), self.convert_term(body_tokens)]

    def parse_parameter(self):
        self.consume('Parameter')
        name = self.consume()
        self.consume(':')
        
        type_tokens = []
        while self.peek() != '.':
            type_tokens.append(self.consume())
        self.consume('.')
        
        return ['Parameter', name, self.convert_term(type_tokens)]

    def parse_variable(self):
        self.consume('Variable')
        name = self.consume()
        self.consume(':')
        type_tokens = []
        while self.peek() != '.':
            type_tokens.append(self.consume())
        self.consume('.')
        return ['Variable', name, self.convert_term(type_tokens)]
    
    def parse_axiom(self):
        self.consume('Axiom')
        name = self.consume()
        self.consume(':')
        
        type_tokens = []
        while self.peek() != '.':
            type_tokens.append(self.consume())
        self.consume('.')
        
        return ['Axiom', name, self.convert_term(type_tokens)]

    def parse_theorem(self):
        # Support Theorem, Lemma, Conjecture
        cmd = self.consume() # Theorem/Lemma...
        name = self.consume()
        self.consume(':')
        
        type_tokens = []
        while self.peek() != '.':
            type_tokens.append(self.consume())
        self.consume('.')
        
        proof_sexp = self.parse_block(end_token='Qed')

        return ['Theorem', name, self.convert_term(type_tokens), proof_sexp]

    def parse_block(self, end_token='Qed'):
        # Parse a sequence of tactics until end_token (Qed or })
        tactics = []
        current_tactic = []

        while self.pos < len(self.tokens):
            t = self.peek()
            
            if t == end_token:
                self.consume()
                if end_token == 'Qed':
                    self.consume('.') # Qed.
                # End of block
                return tactics
            
            elif t == 'Admitted':
                self.consume()
                self.consume('.')
                return 'Admitted'
            
            elif t == '{':
                self.consume()
                # Recursive block
                sub_block = self.parse_block(end_token='}')
                tactics.append(['block'] + sub_block)
                
            elif t == '}':
                # Should have been caught by end_token check if expected
                raise Exception("Unexpected }")

            elif t == '.':
                self.consume()
                # End of current tactic
                if current_tactic:
                    tactics.append(self.parse_specific_tactic(current_tactic))
                current_tactic = []
            
            else:
                self.consume()
                current_tactic.append(t)
        
        return tactics

    def parse_specific_tactic(self, tokens):
        if not tokens:
            return []
        head = tokens[0]
        rest = tokens[1:]

        if head == 'rewrite':
            # rewrite [<-|->] term [at n]
            direction = None
            at_loc = None
            
            # Check direction
            if rest and rest[0] in ['<-', '->']:
                direction = rest[0]
                rest = rest[1:]
            
            # Check at (search from end?)
            # "rewrite H at 1"
            # term part is H
            # "rewrite <- H at 1"
            # term part is H
            
            # Find 'at' in rest
            try:
                at_idx = rest.index('at')
                if at_idx + 1 < len(rest):
                    at_loc = rest[at_idx+1]
                    term_tokens = rest[:at_idx]
                else:
                    term_tokens = rest
            except ValueError:
                term_tokens = rest
            
            res = ['rewrite', self.convert_term(term_tokens)]
            if direction:
                res.append(['dir', direction])
            if at_loc:
                res.append(['at', at_loc])
            return res

        if head == 'claim':
            # claim Name : Type
            # tokens: claim L : A
            if ':' in rest:
                idx = rest.index(':')
                name = rest[0] # Assume simple name
                type_toks = rest[idx+1:]
                return ['claim', name, self.convert_term(type_toks)]
            
        if head == 'intros':
            # intros x y z
            return ['intros'] + self.convert_term(rest)

        if head in ['exact', 'apply', 'assume']:
             return [head, self.convert_term(rest)]
             
        return self.convert_term(tokens)

    def convert_term(self, tokens):
        if not tokens:
            return []

        # let ... in
        if tokens[0] == 'let':
            balance = 0
            try:
                in_idx = next(i for i,t in enumerate(tokens) if t == 'in' and balance == 0)
            except StopIteration:
                in_idx = -1
            if in_idx != -1 and len(tokens) >= 4 and tokens[2] == ':=':
                name = tokens[1]
                val = self.convert_term(tokens[3:in_idx])
                body = self.convert_term(tokens[in_idx+1:])
                return ['let', name, val, body]

        # if ... then ... else ...
        if tokens[0] == 'if':
            balance = 0
            then_idx = else_idx = -1
            for i,t in enumerate(tokens):
                if t in ['(', '{', '[']: balance += 1
                elif t in [')', '}', ']']: balance -= 1
                elif balance == 0 and t == 'then' and then_idx == -1:
                    then_idx = i
                elif balance == 0 and t == 'else' and then_idx != -1:
                    else_idx = i
                    break
            if then_idx != -1 and else_idx != -1:
                cond = self.convert_term(tokens[1:then_idx])
                tbranch = self.convert_term(tokens[then_idx+1:else_idx])
                ebranch = self.convert_term(tokens[else_idx+1:])
                return ['if', cond, tbranch, ebranch]

        # match ... with | p => e ...
        if tokens[0] == 'match':
            balance = 0
            with_idx = -1
            for i,t in enumerate(tokens):
                if t in ['(', '{', '[']: balance += 1
                elif t in [')', '}', ']']: balance -= 1
                elif balance == 0 and t == 'with':
                    with_idx = i
                    break
            if with_idx != -1:
                scrut = self.convert_term(tokens[1:with_idx])
                cases_tokens = tokens[with_idx+1:]
                if cases_tokens and cases_tokens[-1] == 'end':
                    cases_tokens = cases_tokens[:-1]
                cases = []
                curr = []
                for tok in cases_tokens:
                    if tok == '|':
                        if curr:
                            cases.append(curr)
                            curr = []
                    else:
                        curr.append(tok)
                if curr:
                    cases.append(curr)
                parsed_cases = []
                for c in cases:
                    try:
                        arr_idx = c.index('=>')
                    except ValueError:
                        continue
                    pat = self.convert_term(c[:arr_idx])
                    body = self.convert_term(c[arr_idx+1:])
                    parsed_cases.append(['case', pat, body])
                return ['match', scrut, parsed_cases]

        # 1. Handle Binders: forall, fun, exists
        if tokens[0] in ['forall', 'fun', 'exists']:
            binder = tokens[0]
            # Find comma or => (for fun)
            separator = ',' if binder != 'fun' else '=>'
            
            sep_idx = -1
            balance = 0
            for i, t in enumerate(tokens):
                if t in ['(', '{', '[']: balance += 1
                elif t in [')', '}', ']']: balance -= 1
                elif balance == 0 and t == separator:
                    sep_idx = i
                    break
            
            if sep_idx != -1:
                vars_part = tokens[1:sep_idx]
                body_part = tokens[sep_idx+1:]
                
                parsed_vars = self.parse_binders(vars_part)
                parsed_body = self.convert_term(body_part)
                return [binder, parsed_vars, parsed_body]

        # Handle if ... then ... else ...
        if tokens[0] == 'if':
            # Find then and else
            then_idx = -1
            else_idx = -1
            
            # Helper to find tokens at current depth
            balance = 0
            if_depth = 0
            
            for i in range(1, len(tokens)):
                t = tokens[i]
                if t in ['(', '{', '[']: balance += 1
                elif t in [')', '}', ']']: balance -= 1
                elif balance == 0:
                    if t == 'if':
                        if_depth += 1
                    elif t == 'then':
                        if if_depth == 0 and then_idx == -1:
                            then_idx = i
                    elif t == 'else':
                        if if_depth == 0 and else_idx == -1:
                            if then_idx != -1: # else comes after then
                                else_idx = i
                                break # Found matching else, we are done? 
                                # Actually, need to be careful about "if A then if B then C else D else E".
                                # The first else binds to the second if? 
                                # Standard: else binds to nearest if. 
                                # But we are tracking depth. 
                                # if (depth 0) ... then ... else (depth 0).
                                pass
                    elif t == 'in': # let inside if?
                        pass 
                    
                    # Wait, we need to handle `if` explicitly closing scopes? 
                    # "if A then B else C". 
                    # nested: "if A then (if B then C else D) else E"
                    # nested: "if A then if B then C else D else E" -> ambiguous without precedence or 'end'?
                    # Megalodon/Coq associates else with nearest if.
                    # But here we are skipping over nested ifs by counting `if`.
                    # Does Megalodon require `else`? Yes.
                    
                    # If we see 'else' and if_depth > 0, we might decrement?
                    # No, "if ... then ... else" is one block.
                    # When we see 'if', depth++. When we see 'else' corresponding to that if, we don't decrement yet?
                    # Actually, 'else' finishes the 'then' block.
                    # The structure is IF cond THEN then_part ELSE else_part.
                    # So we just need to find the ELSE that corresponds to THIS IF.
                    # Count 'if' and 'else'? 
                    # No, 'then' is the anchor.
                    
                    pass

            # Let's try a simpler counter:
            # Iterate. if 'if': depth++. if 'else': depth--. 
            # We want the 'else' where depth becomes -1 relative to current? 
            # No.
            
            # Correct approach for "if ... then ... else":
            # Scan for 'then' at depth 0.
            # Scan for 'else' at depth 0.
            # But "if A then if B then C else D else E".
            # i=0: if. i=...: then (depth 0).
            # i=...: if (depth 1).
            # i=...: then (depth 1).
            # i=...: else (depth 1 -> 0? No, else belongs to inner if).
            
            # Logic:
            # depth = 0.
            # for i in 1..end:
            #   if 'if': depth++
            #   if 'else': depth--
            #   if 'then': pass (doesn't change nesting logic for else matching?)
            
            # Wait, strict grammar: if c then t else e.
            # If we see `if`, we expect a `then` and an `else`.
            # Finding the matching `then` is easy (first `then` at depth 0 of parens/let/etc).
            # Finding matching `else`:
            # Start after `then`.
            # Scan. If `if`: depth++. If `else`: if depth==0 -> FOUND. else depth--.
            
            # Let's implement this 2-phase scan.
            
            # Phase 1: Find THEN
            balance = 0
            for i in range(1, len(tokens)):
                t = tokens[i]
                if t in ['(', '{', '[']: balance += 1
                elif t in [')', '}', ']']: balance -= 1
                elif balance == 0 and t == 'then':
                    then_idx = i
                    break
            
            if then_idx != -1:
                # Phase 2: Find ELSE starting after THEN
                balance = 0
                nested_if = 0
                for i in range(then_idx + 1, len(tokens)):
                    t = tokens[i]
                    if t in ['(', '{', '[']: balance += 1
                    elif t in [')', '}', ']']: balance -= 1
                    elif balance == 0:
                        if t == 'if':
                            nested_if += 1
                        elif t == 'else':
                            if nested_if == 0:
                                else_idx = i
                                break
                            else:
                                nested_if -= 1
                
                if else_idx != -1:
                    cond = tokens[1:then_idx]
                    then_part = tokens[then_idx+1:else_idx]
                    else_part = tokens[else_idx+1:]
                    
                    return ['if', self.convert_term(cond), self.convert_term(then_part), self.convert_term(else_part)]

        # Handle Set Replacement { ! ... | ... ! }
        # Tokenizer splits { and ! usually.
        if tokens[0] == '{' and len(tokens) > 1 and tokens[1] == '!':
            # Find ! }
            end_idx = -1
            balance = 0
            for i in range(2, len(tokens)):
                t = tokens[i]
                if t == '{': balance += 1
                elif t == '}':
                    if balance == 0:
                        if tokens[i-1] == '!':
                            end_idx = i
                            break
                    else:
                        balance -= 1
            
            if end_idx != -1:
                # Content between { ! and ! }
                # tokens[2 : end_idx-1] (exclude !)
                content = tokens[2:end_idx-1]
                
                # Find |
                bar_idx = -1
                b = 0
                for j in range(len(content)):
                    if content[j] in ['{', '(', '[']: b += 1
                    elif content[j] in ['}', ')', ']']: b -= 1
                    elif b == 0 and content[j] == '|':
                        bar_idx = j
                        break
                
                if bar_idx != -1:
                    term_part = content[:bar_idx]
                    cond_part = content[bar_idx+1:]
                    
                    return ['replace', self.convert_term(term_part), self.convert_term(cond_part)]

        # Handle match ... with ... end
        if tokens[0] == 'match':
            # Find with and end
            with_idx = -1
            end_idx = -1
            
            balance = 0
            depth = 0
            for i in range(1, len(tokens)):
                t = tokens[i]
                if t in ['(', '{', '[']: balance += 1
                elif t in [')', '}', ']']: balance -= 1
                elif balance == 0:
                    if t == 'match':
                        depth += 1
                    elif t == 'end':
                        if depth == 0:
                            end_idx = i
                            break
                        else:
                            depth -= 1
                    elif t == 'with':
                        if depth == 0 and with_idx == -1:
                            with_idx = i
            
            if with_idx != -1 and end_idx != -1:
                scrutinee = tokens[1:with_idx]
                arms_part = tokens[with_idx+1:end_idx]
                
                # Parse arms
                # Arms are separated by |
                # | pat => body | pat => body
                # First | is optional? Usually yes.
                # Split by | at top level
                
                arms = []
                current_arm = []
                balance = 0
                
                # Pre-process: if first token is |, skip it
                start_k = 0
                if arms_part and arms_part[0] == '|':
                    start_k = 1
                
                for k in range(start_k, len(arms_part)):
                    t = arms_part[k]
                    if t in ['(', '{', '[']: balance += 1
                    elif t in [')', '}', ']']: balance -= 1
                    elif balance == 0 and t == '|':
                        arms.append(current_arm)
                        current_arm = []
                        continue
                    current_arm.append(t)
                if current_arm:
                    arms.append(current_arm)
                
                parsed_arms = []
                for arm_tokens in arms:
                    # Split by =>
                    # pat => body
                    arrow_idx = -1
                    b = 0
                    for m in range(len(arm_tokens)):
                        if arm_tokens[m] in ['(', '{', '[']: b += 1
                        elif arm_tokens[m] in [')', '}', ']']: b -= 1
                        elif b == 0 and arm_tokens[m] == '=>':
                            arrow_idx = m
                            break
                    
                    if arrow_idx != -1:
                        pat = arm_tokens[:arrow_idx]
                        body = arm_tokens[arrow_idx+1:]
                        parsed_arms.append([self.convert_term(pat), self.convert_term(body)])
                
                return ['match', self.convert_term(scrutinee), parsed_arms]

        # Handle let ... := ... in ...
        if tokens[0] == 'let':
            # Format: let var [: type] := val in body
            # Find := first
            assign_idx = -1
            balance = 0
            for i, t in enumerate(tokens):
                if t in ['(', '{', '[']: balance += 1
                elif t in [')', '}', ']']: balance -= 1
                elif balance == 0 and t == ':=':
                    assign_idx = i
                    break
            
            if assign_idx != -1:
                # var part: tokens[1:assign_idx]
                var_part = tokens[1:assign_idx]
                
                # Parse var part: "x" or "x : Type"
                var_name = var_part[0]
                var_type = 'Any'
                if len(var_part) > 2 and var_part[1] == ':':
                    var_type = self.convert_term(var_part[2:])
                
                # Find matching 'in'
                in_idx = -1
                balance = 0
                let_depth = 0
                for i in range(assign_idx + 1, len(tokens)):
                    t = tokens[i]
                    if t in ['(', '{', '[']: balance += 1
                    elif t in [')', '}', ']']: balance -= 1
                    elif balance == 0:
                        if t == 'let':
                            let_depth += 1
                        elif t == 'in':
                            if let_depth == 0:
                                in_idx = i
                                break
                            else:
                                let_depth -= 1
                
                if in_idx != -1:
                    val_part = tokens[assign_idx+1:in_idx]
                    body_part = tokens[in_idx+1:]
                    
                    return ['let', [var_name, var_type], self.convert_term(val_part), self.convert_term(body_part)]

        # 2. Precedence-aware parsing for infix/prefix operators (including ->)
        def parse_atom(idx):
            tok = tokens[idx]
            if tok == '(':
                balance = 1
                j = idx + 1
                sub = []
                while j < len(tokens) and balance > 0:
                    if tokens[j] == '(':
                        balance += 1
                    elif tokens[j] == ')':
                        balance -= 1
                    if balance > 0:
                        sub.append(tokens[j])
                    j += 1
                return self.convert_term(sub), j
            return tok, idx + 1

        def parse_prefix(idx):
            if idx < len(tokens):
                tok = tokens[idx]
                if tok in self.prefix_ops:
                    prec = self.prefix_ops[tok]
                    rhs, next_i = parse_expr(idx + 1, prec)
                    return [tok, rhs], next_i
            return parse_atom(idx)

        def parse_expr(idx, max_prec):
            lhs, i = parse_prefix(idx)
            while i < len(tokens):
                op = tokens[i]
                if op in self.infix_ops:
                    prec, assoc = self.infix_ops[op]
                    # Megalodon Logic: Lower number = Tighter binding
                    # If current op is looser (higher number) than context, break
                    if prec > max_prec:
                        break
                    
                    # Calculate new max_prec for RHS
                    # Left assoc: break on equal precedence (tighter limit)
                    # Right assoc: allow equal precedence (same limit)
                    next_max = prec - 1 if assoc == 'left' else prec
                    
                    rhs, j = parse_expr(i + 1, next_max)
                    lhs = [op, lhs, rhs]
                    i = j
                elif op == ')':
                    break
                else:
                    # Treat as application: lhs op
                    # Application binds tightest? Or loosely?
                    # Usually tightest.
                    rhs, j = parse_prefix(i)
                    lhs = [lhs, rhs]
                    i = j
            return lhs, i

        expr, _ = parse_expr(0, 10000)
        return expr

    def parse_binders(self, tokens):
        res = []
        current_vars = []
        i = 0
        while i < len(tokens):
            t = tokens[i]
            if t == '(':
                # Typed binder group (x:A) or (x y : A)
                # Scan until closing paren
                j = i + 1
                group_tokens = []
                balance = 1
                while j < len(tokens) and balance > 0:
                    if tokens[j] == '(': balance += 1
                    elif tokens[j] == ')': balance -= 1
                    if balance > 0:
                        group_tokens.append(tokens[j])
                    j += 1
                
                res.extend(self.parse_binders(group_tokens))
                i = j
            elif t == ':':
                # Everything after colon is the type (up to end of these tokens)
                # Since we are in a binder group (or top level vars before comma), 
                # the rest of 'tokens' IS the type.
                type_tokens = tokens[i+1:]
                type_term = self.convert_term(type_tokens)
                
                for v in current_vars:
                    res.append([v, type_term])
                current_vars = []
                
                # We consumed everything
                break
            else:
                current_vars.append(t)
                i += 1
        
        for v in current_vars:
            res.append([v, 'Any']) 
            
        return res

def sexp_to_str(sexp):
    if isinstance(sexp, list):
        return "(" + " ".join(sexp_to_str(x) for x in sexp) + ")"
    return str(sexp)

DEBUG_FOOTER = [
    '!(println! "=== Definitions in &self ===")',
    '!(match &self (Definition $name $ty $body) ($name $ty))',
    '!(println! "=== Theorems in &self ===")',
    '!(match &self (Theorem $name $ty $proof) ($name $ty))',
    '!(println! "=== Parameters in &self ===")',
    '!(match &self (Parameter $name $ty) ($name $ty))',
    '!(println! "=== Axioms in &self ===")',
    '!(match &self (Axiom $name $ty) ($name $ty))',
]

def main():
    import argparse

    parser = argparse.ArgumentParser(description="Convert Megalodon .mg to MeTTa S-expr")
    parser.add_argument("file", help=".mg source file")
    parser.add_argument(
        "--with-debug-footer",
        action="store_true",
        help="append simple match/println footer for PeTTa visibility",
    )
    args = parser.parse_args()

    with open(args.file, 'r') as f:
        content = f.read()

    tokens = tokenize(content)
    parser = MGParser(tokens)
    exprs = parser.parse_file()

    for expr in exprs:
        print(sexp_to_str(expr))
    if args.with_debug_footer:
        for line in DEBUG_FOOTER:
            print(line)

if __name__ == "__main__":
    main()
