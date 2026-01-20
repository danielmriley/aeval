
import os
import re

def process_file(filepath, out_dir):
    with open(filepath, 'r') as f:
        content = f.read()

    # Regex to find the fail rule and the negation
    # Looking for: (rule (=> (and ... (not (= ...))) fail))
    # We want to remove the (not ...) wrapping the equality or inequality

    # Simple heuristic: The property is the last condition in the fail rule.
    # It usually looks like (not (= ...))
    
    # We will look for "(not (= " and replace with "(= " inside the sequence.
    # But we should be careful not to unrelated nots.
    # In these benchmarks, the structure is very consistent: (not (= variable relation))
    
    if "(not (=" in content:
        new_content = content.replace("(not (=", "(= ")
        # We replaced "(not (=" with "(= ".
        # The original was "(not (= A B))".
        # Now it is "(= A B))".
        # We need to remove one closing paren processing from the end of that S-expr.
        # But wait, replace is string based.
        # "(not (= A B))" -> "(= A B))"
        # We have an extra closing parenthesis now at the end of the term.
        # This is tricky with simple string replace.
        
        # Let's try to match the balanced parentheses.
        # Or better, since these are machine generated or regular:
        # (not (= y0 x0)) -> (= y0 x0)
        
        # Regex replacement might be safer.
        # Match `(not (= A B))` where A and B are anything balanced. 
        # But A and B might be complex.
        
        # Given the previous examples:
        # (not (= y0 x0))
        # (not (= z0 (* 2 x0)))
        
        # Let's write a parser specific to this structure or use regex that handles balanced parens (hard).
        # Actually, for these files, the negation is likely at the very end of the AND block of the FAIL rule.
        
        lines = content.splitlines()
        new_lines = []
        for line in lines:
            if "fail))" in line and "(not (=" in line:
                # This is the line with the assertion.
                # Example: (rule (=> (and (inv x0 y0) (= x0 10000) (not (= y0 x0))) fail))
                # or split across lines.
                
                # Let's try to just remove "(not " and the corresponding ")"
                # It's usually `(not (= ...))`
                # Replacing `(not (=` with `(=` leaves an extra `)` at the end of the term.
                # `(= y0 x0))`
                
                # Regex: `\(not\s+(=.+?)\)`
                # This works if the equality doesn't contain `)` which is false for `(* 2 x0)`.
                
                # Let's simplify. We can find the index of "(not (="
                while "(not (=" in line:
                    start_idx = line.find("(not (=")
                    # Find matching closing paren
                    count = 0
                    end_idx = -1
                    for i in range(start_idx, len(line)):
                        if line[i] == '(':
                            count += 1
                        elif line[i] == ')':
                            count -= 1
                            if count == 0:
                                end_idx = i
                                break
                    
                    if end_idx != -1:
                        # logical_negation = line[start_idx:end_idx+1] # e.g. (not (= a b))
                        # inner = logical_negation[5:-1] # (= a b)
                        # But wait, [5:-1] assumes "(not " is 5 chars.
                        # Check spaces.
                        # "(not " is 5.
                        
                        # Reconstruct line
                        line = line[:start_idx] + line[start_idx+5:end_idx] + line[end_idx+1:]
                    else:
                        break # mismatch or spanning lines (unlikely for these benchs?)
            
            new_lines.append(line)
        
        new_content = "\n".join(new_lines)
        
        filename = os.path.basename(filepath)
        with open(os.path.join(out_dir, filename), 'w') as f_out:
            f_out.write(new_content)
            
    else:
        # Just copy if no negation found (might already be unsafe? or different structure)
        filename = os.path.basename(filepath)
        with open(os.path.join(out_dir, filename), 'w') as f_out:
            f_out.write(content)

def main():
    src_dir = "bench_horn"
    out_dir = "bench_horn_split_cex"
    
    if not os.path.exists(out_dir):
        os.makedirs(out_dir)
        
    for f in os.listdir(src_dir):
        if "s_split" in f and f.endswith(".smt2"):
            process_file(os.path.join(src_dir, f), out_dir)

if __name__ == "__main__":
    main()
