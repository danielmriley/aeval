
import os
import re

def convert_to_bitwidth(content, new_width):
    # 1. Replace type: (_ BitVec 32) -> (_ BitVec new_width)
    content = content.replace("(_ BitVec 32)", f"(_ BitVec {new_width})")
    
    # 2. Replace literals: (_ bvN 32) -> (_ bvN new_width)
    # Be careful with regex to match exactly (_ bv<digits> 32)
    # The regex should capture the value N.
    
    def replacer(match):
        val = match.group(1)
        return f"(_ bv{val} {new_width})"
    
    # Matches (_ bv123 32)
    content = re.sub(r'\(_ bv(\d+) 32\)', replacer, content)
    
    return content

def main():
    src_dir = "bench_horn_split_cex_bv"
    
    files = [f for f in os.listdir(src_dir) if f.endswith(".smt2") and "bv" not in f[:3]] # Avoid processing already processed if run twice (heuristic) or just filter for s_split_*.smt2
    
    # Filter strictly for standard benchmarks structure
    files = [f for f in files if re.match(r"s_split_\d+\.smt2$", f)]
    
    bitwidths = [4, 8, 16, 32, 64]
    
    for bw in bitwidths:
        bw_dir = os.path.join(src_dir, f"bv{bw}")
        if not os.path.exists(bw_dir):
            os.makedirs(bw_dir)
            
    for f in files:
        filepath = os.path.join(src_dir, f)
        with open(filepath, 'r') as fin:
            content = fin.read()
            
        for bw in bitwidths:
            new_content = convert_to_bitwidth(content, bw)
            # Create subfolder name based on original bench name often? 
            # Request: "create subfolders... for each benchmark and create versions... for bitwidths"
            # It usually means:
            # bench_horn_split_cex_bv/
            #   s_split_01/
            #     bv4_s_split_01.smt2
            #     bv8_s_split_01.smt2
            #     ...
            
            # Re-reading prompt: "create subfolders in the new ... folder for each benchmark"
            # Yes, per benchmark folder.
            
            base_name = os.path.splitext(f)[0] # s_split_01
            bench_sub_dir = os.path.join(src_dir, base_name)
            
            if not os.path.exists(bench_sub_dir):
                os.makedirs(bench_sub_dir)
                
            new_filename = f"bv{bw}_{f}"
            
            with open(os.path.join(bench_sub_dir, new_filename), 'w') as fout:
                fout.write(new_content)

if __name__ == "__main__":
    main()
