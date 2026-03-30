import os
import re
import sys

# Module-level uninterpreted function registry, set per file conversion
_uninterp_fns = {}
# Module-level variable width registry: C var name -> BV width, set per file conversion
_var_widths = {}

def parse_smt2(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Remove comments
    content = re.sub(r';.*', '', content)
    
    # Tokenize (simple)
    tokens = content.replace('(', ' ( ').replace(')', ' ) ').split()
    
    return tokens

def parse_sexpr(tokens):
    if not tokens:
        return None
    token = tokens.pop(0)
    if token == '(':
        expr = []
        while tokens[0] != ')':
            expr.append(parse_sexpr(tokens))
        tokens.pop(0) # pop ')'
        return expr
    else:
        return token

def find_relation_decl(sexprs):
    # Look for (declare-rel inv ...) or (declare-fun inv ...)
    for expr in sexprs:
        if isinstance(expr, list) and len(expr) > 1:
            if expr[0] == 'declare-rel' and expr[1] == 'inv':
                return expr
            if expr[0] == 'declare-fun' and expr[1] == 'inv':
                return expr
    return None

def find_uninterp_fns(sexprs):
    # Collect (declare-fun name (args...) (_ BitVec N)) for non-inv functions
    fns = {}
    for expr in sexprs:
        if isinstance(expr, list) and len(expr) >= 4:
            if expr[0] == 'declare-fun' and expr[1] != 'inv':
                ret = expr[3]
                if isinstance(ret, list) and len(ret) == 3 and ret[0] == '_' and ret[1] == 'BitVec':
                    fns[expr[1]] = int(ret[2])
    return fns

def get_vars_and_types(decl):
    # (declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
    # (declare-fun inv ((_ BitVec 4) (_ BitVec 4)) Bool)
    vars_types = []
    if decl[0] == 'declare-rel':
        types = decl[2]
        for i, t in enumerate(types):
            width = int(t[2])
            vars_types.append((f'v{i}', width))
    elif decl[0] == 'declare-fun':
        types = decl[2]
        for i, t in enumerate(types):
            width = int(t[2])
            vars_types.append((f'v{i}', width))
    return vars_types

def translate_expr(expr, var_map, uninterp_fns=None):
    if uninterp_fns is None:
        uninterp_fns = _uninterp_fns
    if isinstance(expr, str):
        if expr in var_map:
            return var_map[expr]
        if expr.startswith('#x'):
            return '0x' + expr[2:]
        if expr.startswith('#b'):
            return str(int(expr[2:], 2))
        if expr == 'true': return '1'
        if expr == 'false': return '0'
        return expr
    
    op = expr[0]
    
    if op == '_':
        if expr[1].startswith('bv'): # (_ bv10 16)
            return expr[1][2:]
        if expr[1] == 'zero_extend': # (_ zero_extend 4)
            # We handle this in the parent call usually, or just cast
            # But here we return a marker or handle it
            return f"ZERO_EXTEND_{expr[2]}"
        if expr[1] == 'extract': # (_ extract high low)
             return f"EXTRACT_{expr[2]}_{expr[3]}"

    args = [translate_expr(e, var_map, uninterp_fns) for e in expr[1:]]
    
    if op == 'and': return f"({' && '.join(args)})"
    if op == 'or': return f"({' || '.join(args)})"
    if op == 'not': return f"!({args[0]})"
    if op == '=': return f"({args[0]} == {args[1]})"
    if op == 'bvadd' or op == '+': return f"({args[0]} + {args[1]})"
    if op == 'bvsub' or op == '-': return f"({args[0]} - {args[1]})"
    if op == 'bvmul' or op == '*': return f"({args[0]} * {args[1]})"
    if op == 'bvudiv' or op == '/': return f"({args[0]} / {args[1]})"
    if op == 'bvurem' or op == '%': return f"({args[0]} % {args[1]})"
    if op == 'bvand': return f"({args[0]} & {args[1]})"
    if op == 'bvor': return f"({args[0]} | {args[1]})"
    if op == 'bvxor': return f"({args[0]} ^ {args[1]})"
    if op == 'bvnot': return f"(~{args[0]})"
    if op == 'bvneg':
        w = _var_widths.get(args[0])
        if w:
            ctype = get_c_type(w)
            return f"({ctype})(0u - ({ctype})({args[0]}))"
        return f"(-{args[0]})"
    if op == 'bvshl': return f"({args[0]} << {args[1]})"
    if op == 'bvlshr': return f"({args[0]} >> {args[1]})"
    if op == 'bvashr': return f"({args[0]} >> {args[1]})"
    if op == 'bvult' or op == '<': return f"({args[0]} < {args[1]})"
    if op == 'bvule' or op == '<=': return f"({args[0]} <= {args[1]})"
    if op == 'bvugt' or op == '>': return f"({args[0]} > {args[1]})"
    if op == 'bvuge' or op == '>=': return f"({args[0]} >= {args[1]})"
    if op == 'ite': return f"({args[0]} ? {args[1]} : {args[2]})"
    if op == 'bv2int': return args[0]
    
    # Handle zero_extend application: ((_ zero_extend n) x)
    if isinstance(op, list) and op[0] == '_' and op[1] == 'zero_extend':
        # Cast to larger type. In C, standard promotion might work, but explicit is better.
        # We don't know the target size easily here without type inference.
        # But usually it's compared to something.
        # For now, just return the argument, assuming C promotion or explicit cast in context.
        # Or cast to uint64_t to be safe.
        return f"((unsigned long long){args[0]})"

    if isinstance(op, list) and op[0] == '_' and op[1] == 'extract':
        high = int(op[2])
        low = int(op[3])
        # ((x >> low) & mask)
        mask = (1 << (high - low + 1)) - 1
        return f"(({args[0]} >> {low}) & {mask})"

    # Uninterpreted function: replace with nondet of appropriate width
    if isinstance(op, str) and op in uninterp_fns:
        width = uninterp_fns[op]
        if width <= 8: return 'nondet_uchar()'
        if width <= 16: return 'nondet_ushort()'
        if width <= 32: return 'nondet_uint()'
        return 'nondet_ulong()'

    return f"UNKNOWN_OP_{op}({', '.join(args)})"

def get_c_type(width):
    if width <= 8: return "uint8_t"
    if width <= 16: return "uint16_t"
    if width <= 32: return "uint32_t"
    if width <= 64: return "uint64_t"
    return "unsigned __int128" # GCC extension

def contains_next_var(e, next_vars_list):
    if isinstance(e, str):
        return e in next_vars_list
    if isinstance(e, list):
        return any(contains_next_var(sub, next_vars_list) for sub in e)
    return False

def extract_assignments(exprs, next_args, var_map):
    assignments = {}
    constraints = []
    
    for expr in exprs:
        is_assignment = False
        if isinstance(expr, list) and expr[0] == '=':
            lhs = expr[1]
            rhs = expr[2]
            
            target_idx = -1
            source_expr = None
            
            if lhs in next_args:
                target_idx = next_args.index(lhs)
                source_expr = rhs
            elif rhs in next_args:
                target_idx = next_args.index(rhs)
                source_expr = lhs
            
            if target_idx != -1 and target_idx not in assignments:
                if not contains_next_var(source_expr, next_args):
                    assignments[target_idx] = translate_expr(source_expr, var_map)
                    is_assignment = True
        
        if not is_assignment:
            constraints.append(translate_expr(expr, var_map))
            
    return assignments, constraints

def convert_file(filepath, outpath):
    global _uninterp_fns, _var_widths
    tokens = parse_smt2(filepath)
    sexprs = []
    while tokens:
        sexprs.append(parse_sexpr(tokens))

    _uninterp_fns = find_uninterp_fns(sexprs)

    decl = find_relation_decl(sexprs)
    # (populated below after vars_types is computed)
    if not decl:
        print(f"Skipping {filepath}: No inv declaration found")
        return

    vars_types = get_vars_and_types(decl)
    state_vars = [v for v, t in vars_types]

    # Build width lookup for all current and next state variables
    _var_widths = {}
    for i, (v, w) in enumerate(vars_types):
        _var_widths[f"v{i}"] = w
        _var_widths[f"next_v{i}"] = w
    
    # Identify rules
    init_rule = None
    trans_rule = None
    fail_rule = None
    
    for expr in sexprs:
        if expr[0] == 'rule':
            body = expr[1] # (=> ... ...)
            if body[0] == '=>':
                premise = body[1]
                conclusion = body[2]
                
                # Check conclusion
                if isinstance(conclusion, list) and conclusion[0] == 'inv':
                    # Could be Init or Trans
                    # Check premise for inv
                    has_inv = False
                    if isinstance(premise, list):
                        if premise[0] == 'inv': has_inv = True
                        elif premise[0] == 'and':
                            for arg in premise[1:]:
                                if isinstance(arg, list) and arg[0] == 'inv':
                                    has_inv = True
                    
                    if has_inv:
                        trans_rule = expr
                    else:
                        init_rule = expr
                elif isinstance(conclusion, list) and conclusion[0] == 'fail':
                    fail_rule = expr
                elif conclusion == 'fail': # (fail) atom
                    fail_rule = expr
                    
        elif expr[0] == 'assert':
            # (assert (forall ... (=> ...)))
            quant = expr[1]
            if quant[0] == 'forall':
                body = quant[2]
                if body[0] == '=>':
                    premise = body[1]
                    conclusion = body[2]
                    
                    # Similar logic
                    if isinstance(conclusion, list) and conclusion[0] == 'inv':
                        has_inv = False
                        if isinstance(premise, list):
                            if premise[0] == 'inv': has_inv = True
                            elif premise[0] == 'and':
                                for arg in premise[1:]:
                                    if isinstance(arg, list) and arg[0] == 'inv':
                                        has_inv = True
                        
                        if has_inv:
                            trans_rule = expr
                        else:
                            init_rule = expr
                    elif conclusion == 'false': # Property violation
                        fail_rule = expr
                    elif isinstance(conclusion, list) and conclusion[0] == 'not':
                         fail_rule = expr

            # Handle simple assertion Init: (assert (inv #x0000))
            elif isinstance(quant, list) and quant[0] == 'inv':
                init_rule = expr

    if not init_rule or not trans_rule or not fail_rule:
        print(f"Skipping {filepath}: Missing rules (Init: {bool(init_rule)}, Trans: {bool(trans_rule)}, Fail: {bool(fail_rule)})")
        return

    # Generate C code
    with open(outpath, 'w') as f:
        f.write("#include <assert.h>\n")
        f.write("#include <stdint.h>\n\n")
        f.write("// CBMC intrinsics\n")
        f.write("unsigned int nondet_uint();\n")
        f.write("unsigned char nondet_uchar();\n")
        f.write("unsigned short nondet_ushort();\n")
        f.write("unsigned long nondet_ulong();\n")
        f.write("void __CPROVER_assume(int);\n\n")
        
        f.write("int main() {\n")
        
        # Declare state variables
        init_vals = {}
        
        # Pre-process Init to find initial values
        init_cond_str = None
        
        if init_rule[0] == 'rule':
            premise = init_rule[1][1]
            conclusion = init_rule[1][2]
            inv_args = conclusion[1:]
            
            var_map = {}
            for i, arg in enumerate(inv_args):
                var_map[arg] = f"v{i}"
            
            # Check for simple equalities in premise
            # (= x0 #x0000)
            # (and (= x0 #x0000) (= y0 #x0000))
            
            exprs = []
            if isinstance(premise, list) and premise[0] == 'and':
                exprs = premise[1:]
            else:
                exprs = [premise]
                
            for expr in exprs:
                if isinstance(expr, list) and expr[0] == '=':
                    lhs = expr[1]
                    rhs = expr[2]
                    
                    target_idx = -1
                    val = None
                    
                    if lhs in inv_args:
                        target_idx = inv_args.index(lhs)
                        val = translate_expr(rhs, {})
                    elif rhs in inv_args:
                        target_idx = inv_args.index(rhs)
                        val = translate_expr(lhs, {})
                        
                    if target_idx != -1:
                        init_vals[target_idx] = val
            
            init_cond_str = translate_expr(premise, var_map)

        elif init_rule[0] == 'assert':
             if isinstance(init_rule[1], list) and init_rule[1][0] == 'inv':
                inv_args = init_rule[1][1:]
                conds = []
                for i, arg in enumerate(inv_args):
                    val = translate_expr(arg, {})
                    init_vals[i] = val
                    conds.append(f"v{i} == {val}")
                init_cond_str = " && ".join(conds)
             else:
                quant_vars = init_rule[1][1]
                premise = init_rule[1][2][1]
                conclusion = init_rule[1][2][2]
                inv_args = conclusion[1:]
                
                var_map = {}
                for i, arg in enumerate(inv_args):
                    var_map[arg] = f"v{i}"
                
                exprs = []
                if isinstance(premise, list) and premise[0] == 'and':
                    exprs = premise[1:]
                else:
                    exprs = [premise]
                    
                for expr in exprs:
                    if isinstance(expr, list) and expr[0] == '=':
                        lhs = expr[1]
                        rhs = expr[2]
                        
                        target_idx = -1
                        val = None
                        
                        if lhs in inv_args:
                            target_idx = inv_args.index(lhs)
                            val = translate_expr(rhs, {})
                        elif rhs in inv_args:
                            target_idx = inv_args.index(rhs)
                            val = translate_expr(lhs, {})
                            
                        if target_idx != -1:
                            init_vals[target_idx] = val

                init_cond_str = translate_expr(premise, var_map)

        for i, (v, width) in enumerate(vars_types):
            ctype = get_c_type(width)
            if i in init_vals:
                f.write(f"    {ctype} v{i} = {init_vals[i]};\n")
            else:
                f.write(f"    {ctype} v{i};\n")
                # If not initialized, assume nondet? Or assume init_cond handles it?
                # If we have init_cond, we can assume it.
                # But better to initialize if possible.
        
        # Only emit assume if we didn't fully initialize
        if len(init_vals) < len(vars_types):
             f.write(f"    __CPROVER_assume({init_cond_str});\n")
        
        f.write("\n    while(1) {\n")
        
        # Process Fail (Property)
        # (rule (=> (and (inv x0 y0) ...) fail))
        # (assert (forall ... (=> (and (inv ...) Error) false)))
        
        fail_cond = None
        
        if fail_rule[0] == 'rule':
            premise = fail_rule[1][1]
            # Premise is (and (inv ...) ErrorCond)
            # We need to extract ErrorCond
            # And map vars from (inv ...) to v0, v1...
            
            inv_expr = None
            error_exprs = []
            
            if premise[0] == 'and':
                for arg in premise[1:]:
                    if isinstance(arg, list) and arg[0] == 'inv':
                        inv_expr = arg
                    else:
                        error_exprs.append(arg)
            elif premise[0] == 'inv':
                inv_expr = premise
                
            if inv_expr:
                inv_args = inv_expr[1:]
                var_map = {}
                for i, arg in enumerate(inv_args):
                    var_map[arg] = f"v{i}"
                
                if error_exprs:
                    if len(error_exprs) == 1:
                        fail_cond = translate_expr(error_exprs[0], var_map)
                    else:
                        conds = [translate_expr(e, var_map) for e in error_exprs]
                        fail_cond = f"({' && '.join(conds)})"
                else:
                    fail_cond = "1" # Unconditional fail if inv reached?
            
        elif fail_rule[0] == 'assert':
            premise = fail_rule[1][2][1]
            # (and (inv ...) Error)
            
            inv_expr = None
            error_exprs = []
            
            if premise[0] == 'and':
                for arg in premise[1:]:
                    if isinstance(arg, list) and arg[0] == 'inv':
                        inv_expr = arg
                    else:
                        error_exprs.append(arg)
            elif premise[0] == 'inv':
                inv_expr = premise
                
            if inv_expr:
                inv_args = inv_expr[1:]
                var_map = {}
                for i, arg in enumerate(inv_args):
                    var_map[arg] = f"v{i}"
                
                if error_exprs:
                    if len(error_exprs) == 1:
                        fail_cond = translate_expr(error_exprs[0], var_map)
                    else:
                        conds = [translate_expr(e, var_map) for e in error_exprs]
                        fail_cond = f"({' && '.join(conds)})"
        
        if fail_cond:
            f.write(f"        assert(!({fail_cond}));\n")
            
        f.write("\n        // Transition\n")
        
        trans_exprs = []
        next_args = []
        var_map = {}
        
        if trans_rule[0] == 'rule':
            premise = trans_rule[1][1]
            conclusion = trans_rule[1][2]
            
            inv_expr = None
            if isinstance(premise, list):
                if premise[0] == 'and':
                    for arg in premise[1:]:
                        if isinstance(arg, list) and arg[0] == 'inv':
                            inv_expr = arg
                        else:
                            trans_exprs.append(arg)
                elif premise[0] == 'inv':
                    inv_expr = premise
            
            if inv_expr:
                for i, arg in enumerate(inv_expr[1:]):
                    var_map[arg] = f"v{i}"
            
            next_args = conclusion[1:]
            
        elif trans_rule[0] == 'assert':
            premise = trans_rule[1][2][1]
            conclusion = trans_rule[1][2][2]
            
            inv_expr = None
            if isinstance(premise, list):
                if premise[0] == 'and':
                    for arg in premise[1:]:
                        if isinstance(arg, list) and arg[0] == 'inv':
                            inv_expr = arg
                        else:
                            trans_exprs.append(arg)
                elif premise[0] == 'inv':
                    inv_expr = premise
            
            if inv_expr:
                for i, arg in enumerate(inv_expr[1:]):
                    var_map[arg] = f"v{i}"
            
            next_args = conclusion[1:]

        # Map next vars
        for i, arg in enumerate(next_args):
            var_map[arg] = f"next_v{i}"

        # Check for top-level OR (Branching)
        branches = []
        if len(trans_exprs) == 1 and isinstance(trans_exprs[0], list) and trans_exprs[0][0] == 'or':
            branches = trans_exprs[0][1:]
            
        if branches:
            # Branching Logic
            f.write("\n        unsigned int choice = nondet_uint();\n")
            for b_idx, branch in enumerate(branches):
                if b_idx > 0: f.write(" else ")
                f.write(f"        if ((choice % {len(branches)}) == {b_idx}) {{\n")
                
                branch_exprs = []
                if isinstance(branch, list) and branch[0] == 'and':
                    branch_exprs = branch[1:]
                else:
                    branch_exprs = [branch]
                
                b_assignments, b_constraints = extract_assignments(branch_exprs, next_args, var_map)
                
                # Check safety for in-place update
                # Safe if:
                # 1. Assignments don't depend on other updated vars (or cyclic)
                # 2. Constraints don't mix old and new vars
                
                is_safe = True
                
                # Check assignment dependencies
                updated_vars = set(b_assignments.keys())
                for idx, val in b_assignments.items():
                    for other_idx in updated_vars:
                        if other_idx != idx and f"v{other_idx}" in val:
                            is_safe = False
                            break
                    if not is_safe: break
                
                # Check constraints
                pre_conds = []
                post_conds = []
                
                if is_safe:
                    for cond in b_constraints:
                        has_next = any(f"next_v{i}" in cond for i in range(len(vars_types)))
                        has_curr = any(f"v{i}" in cond for i in range(len(vars_types))) # This is tricky, v0 is substring of next_v0
                        
                        # Better check: regex or token check?
                        # Simple check: if "next_v" in cond -> post.
                        # If "v" in cond (but not part of next_v) -> pre.
                        
                        # Let's assume if it has next_v, it's post.
                        # If it has v (and we can verify it's not next_v), it's pre.
                        # If both -> unsafe.
                        
                        uses_next = False
                        uses_curr = False
                        
                        for i in range(len(vars_types)):
                            if f"next_v{i}" in cond: uses_next = True
                            # Check for v{i} not preceded by _
                            if re.search(fr"(?<!_)v{i}\b", cond): uses_curr = True
                            
                        if uses_next and uses_curr:
                            is_safe = False
                            break
                        elif uses_next:
                            post_conds.append(cond)
                        else:
                            pre_conds.append(cond)

                if is_safe:
                    # Emit Pre-conditions as part of if/else if possible, or assume
                    # But we are already inside an if (choice).
                    # We can't easily merge into the choice if without restructuring.
                    # Actually we can: if (choice && guard)
                    # But here we are generating the body.
                    
                    # Let's just use 'if (guard)' inside the choice block to avoid assume
                    if pre_conds:
                        cond = " && ".join(pre_conds)
                        f.write(f"            if ({cond}) {{\n")
                        indent = "                "
                    else:
                        indent = "            "
                    
                    # Emit Assignments
                    for idx, val in b_assignments.items():
                        f.write(f"{indent}v{idx} = {val};\n")
                        
                    # Emit Post-conditions (replace next_v with v)
                    if post_conds:
                        cond = " && ".join(post_conds)
                        for i in range(len(vars_types)):
                            cond = cond.replace(f"next_v{i}", f"v{i}")
                        f.write(f"{indent}__CPROVER_assume({cond});\n")
                    
                    if pre_conds:
                        f.write("            }\n")
                        
                else:
                    # Fallback to local next_v vars
                    for i, (v, width) in enumerate(vars_types):
                        if i in b_assignments:
                            ctype = get_c_type(width)
                            f.write(f"            {ctype} next_v{i} = {b_assignments[i]};\n")
                    
                    # Constraints might use next_v or v
                    if b_constraints:
                        cond = " && ".join(b_constraints)
                        f.write(f"            __CPROVER_assume({cond});\n")
                    
                    # Update
                    for idx in b_assignments:
                        f.write(f"            v{idx} = next_v{idx};\n")

                f.write("        }")
            f.write("\n")

        else:
            # Analyze constraints for assignments
            assignments, constraints = extract_assignments(trans_exprs, next_args, var_map)

            # Declare and Initialize next vars
            # Check if we can do direct assignment
            # Direct assignment is safe if:
            # 1. All updates are self-contained (v_i = f(v_i, consts))
            # 2. OR if we can order them (not implemented yet, so we stick to 1)
            
            all_self_contained = True
            for i in assignments:
                # Check if RHS uses any OTHER state variable
                rhs = assignments[i]
                # Simple string check is risky but might work for v0, v1...
                # Better: check if it contains v{j} where j != i
                for j in range(len(vars_types)):
                    if i != j and f"v{j}" in rhs:
                        all_self_contained = False
                        break
                if not all_self_contained: break
                
            if all_self_contained and len(assignments) == len(vars_types) and not constraints:
                 # Direct update
                 for i in range(len(vars_types)):
                     f.write(f"        v{i} = {assignments[i]};\n")
            else:
                # Use next_v vars
                for i, (v, width) in enumerate(vars_types):
                    ctype = get_c_type(width)
                    if i in assignments:
                        f.write(f"        {ctype} next_v{i} = {assignments[i]};\n")
                    else:
                        f.write(f"        {ctype} next_v{i};\n")
                        if width <= 8: f.write(f"        next_v{i} = nondet_uchar();\n")
                        elif width <= 16: f.write(f"        next_v{i} = nondet_ushort();\n")
                        elif width <= 32: f.write(f"        next_v{i} = nondet_uint();\n")
                        else: f.write(f"        next_v{i} = nondet_ulong();\n")

                # Assume remaining constraints
                if constraints:
                    if len(constraints) == 1:
                        trans_cond = constraints[0]
                    else:
                        trans_cond = f"({' && '.join(constraints)})"
                    f.write(f"        __CPROVER_assume({trans_cond});\n")
                    
                f.write("\n        // Update state\n")
                for i in range(len(vars_types)):
                    f.write(f"        v{i} = next_v{i};\n")
            
        f.write("    }\n")
        f.write("    return 0;\n")
        f.write("}\n")

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print("Usage: python convert.py <input_dir> <output_dir>")
        sys.exit(1)
        
    input_dir = sys.argv[1]
    output_dir = sys.argv[2]
    
    for root, dirs, files in os.walk(input_dir):
        for file in files:
            if file.endswith(".smt2") and "_ccex" not in file:
                filepath = os.path.join(root, file)
                # Create relative path structure in output
                rel_path = os.path.relpath(filepath, input_dir)
                out_path = os.path.join(output_dir, rel_path.replace('.smt2', '.c'))
                
                os.makedirs(os.path.dirname(out_path), exist_ok=True)
                
                print(f"Converting {filepath} -> {out_path}")
                try:
                    convert_file(filepath, out_path)
                except Exception as e:
                    print(f"Failed to convert {filepath}: {e}")

