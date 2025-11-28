import sys
import re


class FormatContext:
    def __init__(self):
        self.infix = {}
        self.prefix = {}
        # Default built-ins
        self.add_infix('->', 800, 'right')

    def add_infix(self, op, prec, assoc):
        self.infix[op] = (prec, assoc)

    def add_prefix(self, op, prec):
        self.prefix[op] = prec

def parse_sexp(text):
    # Basic S-expression parser
    text = re.sub(r'\s+', ' ', text)
    text = text.replace('(', ' ( ').replace(')', ' ) ')
    tokens = text.split()
    
    stack = [[]]
    for token in tokens:
        if token == '(':
            stack.append([])
        elif token == ')':
            if len(stack) > 1:
                l = stack.pop()
                stack[-1].append(l)
        else:
            stack[-1].append(token)
    return stack[0]

def sexp_to_mg_term(expr, ctx: FormatContext, parent_prec=10000, side="none"):
    try:
        if isinstance(expr, str):
            return expr
        if not isinstance(expr, list):
            return str(expr)
        if not expr:
            return ""

        head = expr[0]

        if head == 'forall':
            vars_part = unparse_binders(expr[1], ctx)
            body_part = sexp_to_mg_term(expr[2], ctx)
            return f"forall {vars_part}, {body_part}"

        if head == 'exists':
            vars_part = unparse_binders(expr[1], ctx)
            body_part = sexp_to_mg_term(expr[2], ctx)
            return f"exists {vars_part}, {body_part}"

        if head == 'fun':
            if len(expr) < 3:
                 return "(* fun malformed len < 3 *)"
            
            vars_part = unparse_binders(expr[1], ctx, is_fun=True)
            body_part = sexp_to_mg_term(expr[2], ctx)
            return f"fun {vars_part} => {body_part}"

        if head == 'let':
            # Accept both ['let', [name, type], val, body] and ['let', name, val, body]
            if len(expr) >= 4:
                name_expr = expr[1]
                val = sexp_to_mg_term(expr[2], ctx)
                body = sexp_to_mg_term(expr[3], ctx)

                if isinstance(name_expr, list) and name_expr:
                    name = name_expr[0]
                    type_info = name_expr[1] if len(name_expr) >= 2 else 'Any'
                    if type_info == 'Any':
                        return f"let {name} := {val} in {body}"
                    type_str = sexp_to_mg_term(type_info, ctx)
                    return f"let {name} : {type_str} := {val} in {body}"

                if isinstance(name_expr, str):
                    return f"let {name_expr} := {val} in {body}"

            return f"let ? := ? in ?"
        
        if head == 'if':
            if len(expr) >= 4:
                if_prec = 9000
                cond = sexp_to_mg_term(expr[1], ctx, if_prec)
                then_b = sexp_to_mg_term(expr[2], ctx, if_prec)
                else_b = sexp_to_mg_term(expr[3], ctx, if_prec)
                
                out = f"if {cond} then {then_b} else {else_b}"
                
                if if_prec > parent_prec: 
                    return f"({out})"
                return out
            return "if ? then ? else ?"

        if head == 'match':
            if len(expr) >= 3:
                scrutinee = sexp_to_mg_term(expr[1], ctx)
                arms = expr[2]

                lines = [f"match {scrutinee} with"]
                if isinstance(arms, list):
                    for arm in arms:
                        if not isinstance(arm, list) or not arm:
                            continue
                        # Accept either ['case', pat, body] or [pat, body]
                        if arm[0] == 'case' and len(arm) >= 3:
                            pat = arm[1]
                            body = arm[2]
                        elif len(arm) == 2:
                            pat = arm[0]
                            body = arm[1]
                        else:
                            continue
                        pat_str = sexp_to_mg_term(pat, ctx)
                        body_str = sexp_to_mg_term(body, ctx)
                        lines.append(f"| {pat_str} => {body_str}")
                lines.append("end")
                return " ".join(lines)
            return "match ? with ... end"

        if head == 'replace':
            if len(expr) >= 3:
                term = sexp_to_mg_term(expr[1], ctx)
                cond = sexp_to_mg_term(expr[2], ctx)
                return f"{{! {term} | {cond} !}}"
            return "{! ? | ? !}"

        if head == 'intros':
            args = []
            for arg in expr[1:]:
                args.append(sexp_to_mg_term(arg, ctx))
            return f"intros {' '.join(args)}"

        # Tactics
        if head == 'rewrite':
            if len(expr) >= 2:
                term = sexp_to_mg_term(expr[1], ctx)
                parts = ['rewrite']
                
                direction = None
                at_loc = None
                
                for arg in expr[2:]:
                    if isinstance(arg, list) and len(arg) == 2:
                        if arg[0] == 'dir':
                            direction = arg[1]
                        elif arg[0] == 'at':
                            at_loc = arg[1]
                
                if direction:
                    parts.append(direction)
                
                parts.append(term)
                
                if at_loc:
                    parts.append('at')
                    parts.append(str(at_loc))
                    
                return " ".join(parts)
            return "rewrite ?"

        if head == 'claim':
            if len(expr) >= 3:
                name = expr[1]
                type_str = sexp_to_mg_term(expr[2], ctx)
                return f"claim {name} : {type_str}"
            return "claim ?"

        if head == 'block':
            lines = ["{"]
            for tactic in expr[1:]:
                t_str = sexp_to_mg_term(tactic, ctx)
                if not t_str.strip().endswith('}'):
                    t_str += "."
                lines.append("  " + t_str)
            lines.append("}")
            return "\n".join(lines)

        # Check if head is an operator (must be string)
        if isinstance(head, str):
            if head in ctx.prefix and len(expr) == 2:
                prec = ctx.prefix[head]
                sub = sexp_to_mg_term(expr[1], ctx, prec)
                out = f"{head} {sub}"
                if prec > parent_prec:
                    return f"({out})"
                return out

            if head in ctx.infix and len(expr) == 3:
                prec, assoc = ctx.infix[head]
                
                need_paren = prec > parent_prec
                
                if assoc == 'left':
                    lhs_prec = prec 
                    rhs_prec = prec - 1 
                else:
                    lhs_prec = prec - 1 
                    rhs_prec = prec 
                
                lhs = sexp_to_mg_term(expr[1], ctx, lhs_prec, side="left")
                rhs = sexp_to_mg_term(expr[2], ctx, rhs_prec, side="right")
                out = f"{lhs} {head} {rhs}"
                
                if need_paren or (prec == parent_prec and side == "right" and assoc == "left") or (prec == parent_prec and side == "left" and assoc == "right"):
                     return f"({out})"
                return out

        # Application: left-assoc
        rendered = []
        for sub in expr:
            s = sexp_to_mg_term(sub, ctx, parent_prec=0)
            if isinstance(sub, list) and len(sub) > 1:
                s = f"({s})"
            rendered.append(s)
        out = " ".join(rendered)
        return out
    except Exception as e:
        # Catch-all to debug recursion depth or data errors
        # Don't crash the whole conversion
        return f"(* ERROR: {e} on {expr} *)"

def unparse_binders(binders_list, ctx: FormatContext, is_fun=False):
    # ((p prop) (q prop)) -> (p:prop) (q:prop)
    
    if not isinstance(binders_list, list):
        return str(binders_list)
    
    res = []
    for b in binders_list:
        if isinstance(b, list) and len(b) == 2:
            var, type_ = b
            if type_ == 'Any':
                res.append(var)
            else:
                type_str = sexp_to_mg_term(type_, ctx)
                res.append(f"({var}:{type_str})")
        else:
            res.append(str(b))
    return " ".join(res)

def sexp_to_mg(expr, ctx: FormatContext):
    if not expr or not isinstance(expr, list):
        return ""
    
    cmd = expr[0]
    if cmd == 'Definition':
        # (Definition name type body)
        name = expr[1]
        type_str = sexp_to_mg_term(expr[2], ctx)
        body_str = sexp_to_mg_term(expr[3], ctx)
        return f"Definition {name} : {type_str} := {body_str}."
        
    elif cmd == 'Theorem':
        # (Theorem name type proof)
        # Proof might be 'Admitted' string OR a list of tactics
        name = expr[1]
        type_str = sexp_to_mg_term(expr[2], ctx)
        proof_obj = expr[3]
        
        if isinstance(proof_obj, str) and proof_obj.strip() == 'Admitted':
             return f"Theorem {name} : {type_str}.\nAdmitted."
        
        # List of tactics
        proof_lines = []
        if isinstance(proof_obj, list):
            for tactic in proof_obj:
                t_str = sexp_to_mg_term(tactic, ctx)
                if not t_str.strip().endswith('}'):
                    t_str += "."
                proof_lines.append(t_str)
        else:
             # Fallback
             proof_lines.append(sexp_to_mg_term(proof_obj, ctx))

        proof_str = "\n".join(proof_lines)
        return f"Theorem {name} : {type_str}.\n{proof_str}\nQed."

    elif cmd == 'Parameter':
        # (Parameter name type)
        name = expr[1]
        type_str = sexp_to_mg_term(expr[2], ctx)
        return f"Parameter {name} : {type_str}."

    elif cmd == 'Variable':
        name = expr[1]
        type_str = sexp_to_mg_term(expr[2], ctx)
        return f"Variable {name} : {type_str}."

    elif cmd == 'Axiom':
        # (Axiom name type)
        name = expr[1]
        type_str = sexp_to_mg_term(expr[2], ctx)
        return f"Axiom {name} : {type_str}."
        
    elif cmd in ['Infix', 'Prefix', 'Binder', 'Binder+', 'Title', 'Author', 'Salt', 'Opaque', 'Transparent', 'Unicode', 'Section', 'End']:
        # (Command arg1 arg2 ...)
        # Reconstruct by joining args
        # args are just strings usually, but might be sexps? 
        # In mg_to_metta we stored them as list of strings/tokens.
        # But metta_to_mg parses everything into nested lists.
        # So args might be atoms or lists.
        
        args = []
        for arg in expr[1:]:
            args.append(sexp_to_mg_term(arg, ctx))

        if cmd == 'Infix' and len(expr) >= 4:
            try:
                op = args[0]
                prec = int(args[1])
                assoc = args[2]
                ctx.add_infix(op, prec, assoc)
            except Exception:
                pass
        if cmd == 'Prefix' and len(expr) >= 3:
            try:
                op = args[0]
                prec = int(args[1])
                ctx.add_prefix(op, prec)
            except Exception:
                pass
        
        return f"{cmd} {' '.join(args)}."

    else:
        return f"(* Unknown command: {cmd} *)"

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 metta_to_mg.py <file.metta>")
        return

    with open(sys.argv[1], 'r') as f:
        content = f.read()

    exprs = parse_sexp(content)
    ctx = FormatContext()

    for expr in exprs:
        print(sexp_to_mg(expr, ctx))
        print("") # Newline between items

if __name__ == "__main__":
    main()
