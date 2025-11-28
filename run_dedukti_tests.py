#!/usr/bin/env python3
import argparse
import glob
import os
import subprocess
import sys
import tempfile

try:
    import resource
except ImportError:  # pragma: no cover - Windows/unsupported
    resource = None

# Configuration
PROJECT_ROOT = os.path.dirname(os.path.abspath(__file__))
VAMPIRE_BIN = os.path.join(PROJECT_ROOT, "vampire/build/vampire")
DEDUKIT_SCRIPT = os.path.join(PROJECT_ROOT, "tools/dedukti.py")
MEGALODON_BIN = os.path.join(PROJECT_ROOT, "megalodon/bin/megalodon")
PREAMBLE = os.path.join(PROJECT_ROOT, "megalodon/examples/egal/PfgEJun2022Preamble.mgs")
PREAMBLE_MIZAR = os.path.join(PROJECT_ROOT, "megalodon/examples/mizar/PfgMizarNov2020Preamble.mgs")
NEQ_LEMMAS = os.path.join(PROJECT_ROOT, "megalodon/ramsey36/neq_lemmas_pure.mgs")
DK_PRELUDE = os.path.join(PROJECT_ROOT, "megalodon/tests/dedukti_bridge/dk_prelude.mg")
TEST_DIR = os.path.join(PROJECT_ROOT, "megalodon/tests/dedukti_bridge")
# Ramsey TPTP directory (Mizar theory)
RAMSEY_TPTP_DIR = os.path.join(PROJECT_ROOT, "megalodon/ramsey36/tptp")

def parse_args():
    parser = argparse.ArgumentParser(description="Vampire -> Dedukti -> Megalodon pipeline runner")
    parser.add_argument(
        "--include-sh",
        action="store_true",
        help="Include stress .sh tests (requires memory cap)",
    )
    parser.add_argument(
        "--max-mem-mb",
        type=int,
        default=None,
        help="Set RLIMIT_AS (soft+hard) before running; recommended 8000 for stress tests",
    )
    parser.add_argument(
        "--force-uncapped-sh",
        action="store_true",
        help="Allow .sh tests without a memory cap (not recommended)",
    )
    return parser.parse_args()

def set_memory_limit(max_mem_mb):
    if not resource or max_mem_mb is None:
        return
    max_bytes = max_mem_mb * 1024 * 1024
    try:
        resource.setrlimit(resource.RLIMIT_AS, (max_bytes, max_bytes))
        print(f"Set memory limit: {max_mem_mb} MB")
    except (ValueError, OSError) as e:  # pragma: no cover - system dependent
        print(f"Warning: failed to set memory limit to {max_mem_mb} MB: {e}")

def has_memory_cap():
    if not resource:
        return True
    try:
        soft, _ = resource.getrlimit(resource.RLIMIT_AS)
    except (ValueError, OSError):  # pragma: no cover - system dependent
        return True
    return soft != resource.RLIM_INFINITY

def run_command(cmd, shell=False, capture_output=True):
    try:
        result = subprocess.run(
            cmd, 
            shell=shell, 
            check=True, 
            capture_output=capture_output, 
            text=True
        )
        return result
    except subprocess.CalledProcessError as e:
        print(f"Error running command: {cmd}")
        print("STDOUT:", e.stdout)
        print("STDERR:", e.stderr)
        return None

def run_test(test_path):
    print(f"Running test: {test_path}")

    # Shell-driven tests (.sh) handle their own pipeline
    if test_path.endswith(".sh"):
        res = subprocess.run(["bash", test_path])
        if res.returncode != 0:
            print("  Shell test failed!")
            return False
        print("  SUCCESS!")
        return True

    base_name, ext = os.path.splitext(test_path)
    dk_file = f"{base_name}.dk"
    mg_file = f"{base_name}.mg"

    # 1. Produce Dedukti
    if ext == ".p":
        print("  1. Vampire -> Dedukti")
        vampire_cmd = [os.path.abspath(VAMPIRE_BIN), "-p", "dedukti", "--proof_extra", "full", test_path]
        with open(dk_file, "w") as f:
            res = subprocess.run(vampire_cmd, stdout=f, stderr=subprocess.PIPE, text=True)
        if res.returncode != 0:
            print("  Vampire failed!")
            print(res.stderr)
            return False
    elif ext == ".dk":
        dk_file = test_path
        print("  1. Dedukti input provided")
    else:
        print(f"  Unsupported file type: {ext}")
        return False
        
    # 2. Dedukti -> Megalodon
    print("  2. Dedukit -> Megalodon")
    dedukit_cmd = [sys.executable, DEDUKIT_SCRIPT, dk_file]
    with open(mg_file, "w") as f:
        res = subprocess.run(dedukit_cmd, stdout=f, stderr=subprocess.PIPE, text=True)
    if res.returncode != 0:
        print("  Dedukit failed!")
        print(res.stderr)
        return False

    # 3. Megalodon Verification
    print("  3. Megalodon Verification")
    # Decide theory/preamble by path or suffix
    is_mizar = test_path.endswith("_mizar.p") or RAMSEY_TPTP_DIR in test_path
    includes = [os.path.abspath(PREAMBLE)]
    if is_mizar:
        includes = [os.path.abspath(PREAMBLE_MIZAR), os.path.abspath(NEQ_LEMMAS)]
    megalodon_cmd = [os.path.abspath(MEGALODON_BIN)]
    if is_mizar:
        megalodon_cmd.append("-mizar")
    megalodon_cmd += sum(([ "-I", inc ] for inc in includes), [])

    # Combine dk_prelude (contains lemmas with proofs) with the generated .mg
    with open(os.path.abspath(DK_PRELUDE), "r") as f:
        dk_prelude_src = f.read()
    with open(os.path.abspath(mg_file), "r") as f:
        mg_src = f.read()

    combined_fd, combined_path = tempfile.mkstemp(suffix=".mg", prefix="dk_run_")
    try:
        with os.fdopen(combined_fd, "w") as f:
            f.write(dk_prelude_src)
            f.write("\n")
            f.write(mg_src)

        res = run_command(megalodon_cmd + [combined_path])
    finally:
        try:
            os.remove(combined_path)
        except OSError:
            pass
    
    if res:
        print("  SUCCESS!")
        return True
    else:
        print("  FAILED Verification")
        return False

def main():
    args = parse_args()
    if not os.path.exists(VAMPIRE_BIN):
        print(f"Vampire binary not found at {VAMPIRE_BIN}")
        sys.exit(1)
    
    if not os.path.exists(MEGALODON_BIN):
        print(f"Megalodon binary not found at {MEGALODON_BIN}")
        sys.exit(1)

    # Default: skip .sh stress tests unless explicitly requested
    env_skip = os.environ.get("DEDUSKIP_SH")
    env_run = os.environ.get("DEDU_RUN_SH")
    skip_sh = True
    if env_skip is not None:
        skip_sh = env_skip not in ("0", "false", "", "no")
    if env_run in ("1", "true", "yes"):
        skip_sh = False
    if args.include_sh:
        skip_sh = False

    test_files = sorted(glob.glob(os.path.join(TEST_DIR, "*.p")))
    # Only run hand-authored .dk fixtures, not auto-generated archives
    dk_allow = ["test_rewrite.dk", "test_bind.dk", "test_triple_neg.dk"]
    for name in dk_allow:
        path = os.path.join(TEST_DIR, name)
        if os.path.exists(path):
            test_files.append(path)
    # Add selected Ramsey TPTP problems (Mizar theory)
    ramsey_targets = [
        "degree_bound_simple.p",
        "neighborhood_indep.p",
        "r34_upper_degree_bound.p",
        "k18_case_analysis.p",
    ]
    for fname in ramsey_targets:
        path = os.path.join(RAMSEY_TPTP_DIR, fname)
        if os.path.exists(path):
            test_files.append(path)

    # Memory guard for stress tests
    max_mem_env = os.environ.get("DEDUMAXMEM_MB")
    max_mem_mb = args.max_mem_mb or (int(max_mem_env) if max_mem_env else None)
    if not skip_sh and max_mem_mb is None:
        max_mem_mb = 8000
    if max_mem_mb:
        set_memory_limit(max_mem_mb)

    if not skip_sh:
        if not has_memory_cap() and not args.force_uncapped_sh and os.environ.get("DEDUSH_FORCE_UNCAPPED") != "1":
            print("Refusing to run .sh stress tests without a memory cap.")
            print("Set a limit first, e.g.: ulimit -Sv 8000000")
            print("Or rerun with --max-mem-mb 8000 or --force-uncapped-sh if you know what you're doing.")
            sys.exit(1)
        test_files += sorted(glob.glob(os.path.join(TEST_DIR, "*.sh")))
    if not test_files:
        print(f"No test files found in {TEST_DIR}")
        sys.exit(1)
        
    success_count = 0
    for t in test_files:
        if run_test(t):
            success_count += 1
            
    print(f"\nSummary: {success_count}/{len(test_files)} tests passed.")

if __name__ == "__main__":
    main()
