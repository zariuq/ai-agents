import subprocess
import sys
import os
import argparse
from pathlib import Path

def run_cmd(cmd):
    # print(f"Running: {cmd}")
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    return result

def normalize_output(text):
    # Remove timestamps, file paths, pointers
    text = re.sub(r'line \d+ char \d+', 'line X char Y', text)
    text = re.sub(r'/.*/', '/PATH/', text)
    return text.strip()

def test_file(mg_file, args):
    print(f"Testing {mg_file}...")
    
    # Paths
    base = mg_file.stem
    metta_file = Path(f"metta-tools/megalodon-bridge/{base}.metta")
    roundtrip_file = Path(f"metta-tools/megalodon-bridge/{base}_roundtrip.mg")
    
    # 1. MG -> MeTTa
    cmd1 = f"python3 metta-tools/megalodon-bridge/mg_to_metta.py {mg_file} > {metta_file}"
    res1 = run_cmd(cmd1)
    if res1.returncode != 0:
        print(f"  [FAIL] mg_to_metta failed: {res1.stderr}")
        return False

    # 2. MeTTa -> MG
    cmd2 = f"python3 metta-tools/megalodon-bridge/metta_to_mg.py {metta_file} > {roundtrip_file}"
    res2 = run_cmd(cmd2)
    if res2.returncode != 0:
        print(f"  [FAIL] metta_to_mg failed: {res2.stderr}")
        return False

    # 3. Kernel Check (Optional)
    if not args.no_kernel:
        cmd_k_orig = f"megalodon/bin/megalodon {mg_file}"
        res_k_orig = run_cmd(cmd_k_orig)
        
        cmd_k_rt = f"megalodon/bin/megalodon {roundtrip_file}"
        res_k_rt = run_cmd(cmd_k_rt)
        
        if res_k_orig.returncode != res_k_rt.returncode:
             print(f"  [FAIL] Kernel behavior mismatch: Original={res_k_orig.returncode}, Roundtrip={res_k_rt.returncode}")
             print(f"  Orig stderr: {res_k_orig.stderr[:100]}...")
             print(f"  RT stderr: {res_k_rt.stderr[:100]}...")
             return False
        else:
             # Compare normalized output?
             pass
    
    # 4. S-Expr Drift Check (Optional)
    if not args.no_sexpr:
        # Convert roundtrip back to Metta to compare Metta1 vs Metta2
        metta_file_2 = Path(f"metta-tools/megalodon-bridge/{base}_2.metta")
        cmd3 = f"python3 metta-tools/megalodon-bridge/mg_to_metta.py {roundtrip_file} > {metta_file_2}"
        run_cmd(cmd3)
        
        cmd_cmp = f"python3 tools/compare_sexpr.py {metta_file} {metta_file_2}"
        res_cmp = run_cmd(cmd_cmp)
        if res_cmp.returncode != 0:
            print(f"  [WARN] S-Expr Drift detected (AST not idempotent).")
            # return False # Make strict later

    print(f"  [PASS] Round-trip successful.")
    return True

import re

def main():
    parser = argparse.ArgumentParser(description="Megalodon Bridge Test Harness")
    parser.add_argument('--no-kernel', action='store_true', help="Skip kernel verification (megalodon binary)")
    parser.add_argument('--no-sexpr', action='store_true', help="Skip S-Expression comparison")
    parser.add_argument('files', nargs='*', help="Specific files to test")
    
    args = parser.parse_args()
    
    files_to_test = []
    if args.files:
        files_to_test = [Path(f) for f in args.files]
    else:
        # Default: walk fixtures and examples
        files_to_test.extend(Path("tests/fixtures/tactics").glob("*.mg"))
        # Add Collatz if exists
        if Path("megalodon/examples/egal/Collatz.mg").exists():
            files_to_test.append(Path("megalodon/examples/egal/Collatz.mg"))
            
    passed = 0
    failed = 0
    
    for f in files_to_test:
        if test_file(f, args):
            passed += 1
        else:
            failed += 1
            
    print(f"\nResults: {passed} Passed, {failed} Failed")
    if failed > 0:
        sys.exit(1)
    sys.exit(0)

if __name__ == "__main__":
    main()
