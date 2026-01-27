
import os
import re

def to_bv_const(val_str):
    val = int(val_str)
    if val >= 0:
        return f"(_ bv{val} 32)"
    else:
        # Negative literal
        return f"(bvneg (_ bv{-val} 32))"

def process_content(content):
    # 1. Replace types
    # (Int means Int type. 
    # Be careful not to replace Int inside names if any (unlikely).
    # Use regex bound or simple replace if safe.
    # In declare-rel and declare-var, Int is usually surrounded by spaces or parens
    
    # Replace "(Int" with "((_ BitVec 32)" ?? No (Int Int) -> ((_ BitVec 32) (_ BitVec 32))
    # Replace " Int)" with " (_ BitVec 32))"
    # Replace " Int " with " (_ BitVec 32) "
    
    # Safe bet: Replace "Int" with "(_ BitVec 32)" strictly tokenized
    # Check if there are other usages of Int?
    content = re.sub(r'\bInt\b', '(_ BitVec 32)', content)
    
    # 2. Operators mapping
    # Simple ops
    ops_map = {
        '+': 'bvadd',
        '*': 'bvmul',
        'div': 'bvsdiv', # SMT2 Int division
        'mod': 'bvsrem',
        '<': 'bvslt',
        '<=': 'bvsle',
        '>': 'bvsgt',
        '>=': 'bvsge'
    }
    
    # We need to tokenize to safely replace ops (avoid inside strings/comments)
    # But simple regex replacement of `(op ` works well for SMT2 prefix notation.
    # e.g. `(+ ` -> `(bvadd `
    
    for op, bvop in ops_map.items():
        # Escape special regex chars like + *
        esc_op = re.escape(op)
        # Look for open paren, spaces, op, boundary
        # SMT2: (+ x y) or ( + x y )
        # Regex: \(\s*op\s+
        pattern = r'\(\s*' + esc_op + r'(?=\s)'
        replacement = f'({bvop}'
        content = re.sub(pattern, replacement, content)
        
    # 3. Subtraction (-) handling
    # (- 100) -> (bvneg 100)
    # (- a b) -> (bvsub a b)
    # This involves basic parsing to check arity.
    # However, since `s_split` is regular, maybe we can hack?
    # NO, (- y0) and (- y0 1) are distinct.
    # Since I don't want to leverage a full parser, I'll assume:
    # If I see `(- arg1)`, it's neg, `(- arg1 arg2)` is sub.
    # I can try to use a slightly smarter token iteration.
    
    # 4. Integer Literals
    # Replace 123 with (_ bv123 32)
    # Replace -123 with (bvneg (_ bv123 32))
    # Note: -123 might be a token in SMT2 or (- 123)
    # If it is a token like `-100`, regex `(?<!\w)-?\d+(?!\w)`
    
    def num_replacer(match):
        val = match.group(0)
        return to_bv_const(val)
        
    # Be careful not to match inside (_ bv... ) which we just added?
    # Or variable names like x0.
    # So assertions: not preceded by `bv`, not part of `x1`.
    
    # Better strategy: Tokenize everything.
    
    tokens = content.replace('(', ' ( ').replace(')', ' ) ').split()
    new_tokens = []
    
    i = 0
    while i < len(tokens):
        t = tokens[i]
        
        # Check for (-) ambiguity
        if t == '-':
            # Look ahead?
            # It's always prefix: ( - ... )
            # Count arguments to closing paren? 
            # We are in a flat list of tokens.
            # We need to parse structure to count args.
            pass

    # Reverting to full recursive parsing for robustness.
    pass

# Simple S-Expression Parser/Transformer
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
            
    return stack[0].children # Return list of top-level commands

def transform_sexp(node):
    if not node.is_list:
        val = node.value
        # 1. Literals
        # Check if integer
        if re.match(r'^-?\d+$', val):
            # It's an integer literal
            # Convert to (_ bvN 32) or (bvneg ...)
            n = int(val)
            if n >= 0:
                return Sexp(f"(_ bv{n} 32)", False)
            else:
                # -100
                # (bvneg (_ bv100 32)) is a list
                neg_node = Sexp("", True)
                neg_node.children.append(Sexp("bvneg", False))
                neg_node.children.append(Sexp(f"(_ bv{-n} 32)", False))
                return neg_node
        
        # 2. Type Int -> (_ BitVec 32)
        if val == "Int":
            return Sexp("(_ BitVec 32)", False)
            
        return node
    
    # It is a list
    if not node.children:
        return node
        
    # Process children first? No, context matters (like declaring vars)
    # Actually recursion first is easy for leaves.
    
    # Handle Ops
    head = node.children[0]
    if not head.is_list:
        op = head.value
        if op in ['+', '*', '<', '<=', '>', '>=', 'div', 'mod']:
             # Map op
            ops_map = {
                '+': 'bvadd',
                '*': 'bvmul',
                'div': 'bvsdiv',
                'mod': 'bvsrem',
                '<': 'bvslt',
                '<=': 'bvsle',
                '>': 'bvsgt',
                '>=': 'bvsge'
            }
            node.children[0].value = ops_map[op]
            
        if op == '-':
            # Unary vs Binary
            # Count non-list children or total children?
            # Arity: (- a) vs (- a b)
            # Recursively transform args first to resolve literals?
            # Yes.
            pass
            
    # Recurse
    new_children = []
    for c in node.children:
        new_children.append(transform_sexp(c))
    node.children = new_children
    
    # Post-process list after children transformed
    head = node.children[0]
    if not head.is_list:
        op = head.value
        if op == '-':
            # Check arity (minus head)
            if len(node.children) == 2: # (- arg)
                node.children[0].value = "bvneg"
            elif len(node.children) == 3: # (- a b)
                node.children[0].value = "bvsub"
            else:
                # (- a b c) -> not standard in CHC typically but SMT2 allows (- a b c) as sub?
                # Actually SMT2 (- a b c) is (- (- a b) c).
                # BV ops are binary. We might need to unroll.
                # But let's assume binary for now or `bvsub` only takes 2 args.
                # If mulitple args, nested bvsub.
                # Let's hope s_split doesn't do (- a b c).
                pass
                
        # Also need to handle chaining + * for BV?
        # (+ a b c) -> (bvadd (bvadd a b) c)
        if op in ['bvadd', 'bvmul'] and len(node.children) > 3:
            # Need to nest
            # (op a b c) -> (op (op a b) c)
            orig_op = head.value
            args = node.children[1:]
            
            # Create nested structure
            curr = Sexp("", True)
            curr.children = [Sexp(orig_op, False), args[0], args[1]]
            
            for arg in args[2:]:
                wrapper = Sexp("", True)
                wrapper.children = [Sexp(orig_op, False), curr, arg]
                curr = wrapper
                
            return curr

    return node

import sys

def main():
    if len(sys.argv) == 3:
        # Single file mode
        src_file = sys.argv[1]
        dst_file = sys.argv[2]
        
        with open(src_file, 'r') as fin:
            content = fin.read()
            
        tokens = content.replace('(', ' ( ').replace(')', ' ) ').split()
        sexps = parse_sexp(tokens)
        
        new_sexps = [transform_sexp(s) for s in sexps]
        
        with open(dst_file, 'w') as fout:
            for s in new_sexps:
                fout.write(str(s) + "\n")
        return

    src_dir = "bench_horn_split_cex"
    out_dir = "bench_horn_split_cex_bv"
    
    if not os.path.exists(out_dir):
        os.makedirs(out_dir)
        
    for f in os.listdir(src_dir):
        if f.endswith(".smt2"):
            with open(os.path.join(src_dir, f), 'r') as fin:
                content = fin.read()
                
            # Parse
            # Pre-tokenize: add spaces around parens
            tokens = content.replace('(', ' ( ').replace(')', ' ) ').split()
            sexps = parse_sexp(tokens)
            
            # Transform
            new_sexps = [transform_sexp(s) for s in sexps]
            
            # Print back
            with open(os.path.join(out_dir, f), 'w') as fout:
                for s in new_sexps:
                    fout.write(str(s) + "\n")

if __name__ == "__main__":
    main()
