import sys
import re

def normalize_sexp_str(s):
    # Remove whitespace, newlines
    s = re.sub(r'\s+', ' ', s).strip()
    # Ensure spaces around parens for simple tokenization
    s = s.replace('(', ' ( ').replace(')', ' ) ')
    return s.split()

def compare_files(file1, file2):
    with open(file1, 'r') as f1, open(file2, 'r') as f2:
        c1 = f1.read()
        c2 = f2.read()
        
    tokens1 = normalize_sexp_str(c1)
    tokens2 = normalize_sexp_str(c2)
    
    if tokens1 == tokens2:
        return True
    
    # Find diff
    limit = min(len(tokens1), len(tokens2))
    for i in range(limit):
        if tokens1[i] != tokens2[i]:
            print(f"Difference at token {i}: '{tokens1[i]}' vs '{tokens2[i]}'")
            context_start = max(0, i - 5)
            context_end = min(limit, i + 5)
            print(f"Context 1: ... {' '.join(tokens1[context_start:context_end])} ...")
            print(f"Context 2: ... {' '.join(tokens2[context_start:context_end])} ...")
            return False
            
    if len(tokens1) != len(tokens2):
        print(f"Length mismatch: {len(tokens1)} vs {len(tokens2)}")
        return False
        
    return True

def main():
    if len(sys.argv) < 3:
        print("Usage: python3 compare_sexpr.py <file1.metta> <file2.metta>")
        sys.exit(1)
        
    if compare_files(sys.argv[1], sys.argv[2]):
        print("Files match structurally.")
        sys.exit(0)
    else:
        print("Files do NOT match.")
        sys.exit(1)

if __name__ == "__main__":
    main()
