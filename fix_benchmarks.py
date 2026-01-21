
import os
import re
import sys

class Sexp:
    def __init__(self, value, is_list=False):
        self.value = value
        self.is_list = is_list
        self.children = []

    def __repr__(self):
        if self.is_list:
            return "(" + " ".join([str(c) for c in self.children]) + ")"
        return self.value

def parse_sexp(tokens):
    stack = [Sexp("", True)] # Root list
    current = stack[0]
    
    for t in tokens:
        if t == '(':
            new_node = Sexp("", True)
            current.children.append(new_node)
            stack.append(new_node)
            current = new_node
        elif t == ')':
            stack.pop()
            if not stack:
                raise ValueError("Unbalanced parentheses")
            current = stack[-1]
        else:
            current.children.append(Sexp(t, False))
            
    return stack[0].children

def load_sexp_from_file(path):
    with open(path, 'r') as f:
        content = f.read()
    # Tokenize
    tokens = content.replace('(', ' ( ').replace(')', ' ) ').split()
    return parse_sexp(tokens)

def get_fail_rule_condition(sexps):
    # Returns (RuleSexp, AndListSexp)
    # Looking for: (rule (=> (and ... ) fail))
    for s in sexps:
        if s.is_list and s.children and s.children[0].value == 'rule':
            # Structure: (rule (=> LHS fail))
            # s.children[1] is (=> LHS fail)
            implies = s.children[1]
            if implies.is_list and implies.children[0].value == '=>':
                targets = implies.children[2] 
                # Target could be fail or (fail) ? usually fail atom.
                if targets.value == 'fail' or (targets.is_list and targets.children and targets.children[0].value == 'fail'):
                    lhs = implies.children[1]
                    # LHS should be (and ...)
                    if lhs.is_list and lhs.children and lhs.children[0].value == 'and':
                        return s, lhs
    return None, None

def negate_term(term):
    # If (not X) -> X
    # Else -> (not term)
    if term.is_list and term.children and term.children[0].value == 'not':
        return term.children[1]
    
    new_node = Sexp("", True)
    new_node.children.append(Sexp("not", False))
    new_node.children.append(term)
    return new_node

def main():
    bench_dir = "bench_horn"
    cex_dir = "bench_horn_split_cex"
    
    fixed_count = 0
    
    for f in sorted(os.listdir(bench_dir)):
        if not f.startswith("s_split") or not f.endswith(".smt2"):
            continue
            
        orig_path = os.path.join(bench_dir, f)
        cex_path = os.path.join(cex_dir, f)
        
        if not os.path.exists(cex_path):
            print(f"Skipping {f}, not in cex dir")
            continue
            
        orig_sexps = load_sexp_from_file(orig_path)
        cex_sexps = load_sexp_from_file(cex_path)
        
        orig_rule, orig_cond = get_fail_rule_condition(orig_sexps)
        cex_rule, cex_cond = get_fail_rule_condition(cex_sexps)
        
        if not orig_rule or not cex_rule:
            print(f"Checking {f}: Could not find fail rule in one of the files")
            continue
            
        # Compare string representations of the conditions
        # Note: we compare the *Logic* part.
        # Structure of AND: (and (inv ...) C1 C2 ...)
        # We compare the list of children.
        
        # Simple check: equal string?
        if str(orig_cond) == str(cex_cond):
            print(f"Fixing {f}: Conditions identical. Negating last conjunct.")
            
            # Negate last child of cex_cond
            conjuncts = cex_cond.children
            if len(conjuncts) < 2:
                # (and (inv ...)) ? No other condition?
                print(f"  Warning: {f} has no additional constraints to negate.")
                continue
                
            last_term = conjuncts[-1]
            new_last = negate_term(last_term)
            cex_cond.children[-1] = new_last
            
            # Write back
            with open(cex_path, 'w') as fout:
                for s in cex_sexps:
                    fout.write(str(s) + "\n")
            
            fixed_count += 1
        else:
            # print(f"Skipping {f}: already different.")
            pass
            
    print(f"Total fixed: {fixed_count}")

if __name__ == "__main__":
    main()
