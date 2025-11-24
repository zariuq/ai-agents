#!/usr/bin/env python3
"""
Round-trip oracle harness for the Megalodon <-> MeTTa bridge.

For each `.mg` file:
  1. mg -> metta
  2. metta -> mg (round-trip)
  3. Optional: run Megalodon kernel on both originals and round-trips
  4. Optional: compare S-exprs for structural drift
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Optional

BRIDGE_ROOT = Path(__file__).resolve().parents[1]
# Prefer the workspace root that actually contains megalodon.
DEFAULT_WORKSPACE_ROOT = BRIDGE_ROOT.parents[1]
MG_TO_METTA = BRIDGE_ROOT / "mg_to_metta.py"
METTA_TO_MG = BRIDGE_ROOT / "metta_to_mg.py"
DEFAULT_MEGALODON_BIN = DEFAULT_WORKSPACE_ROOT / "megalodon" / "bin" / "megalodon"

sys.path.append(str(BRIDGE_ROOT / "tools"))
try:
    from compare_sexpr import diff as sexpr_diff, parse_sexpr
except Exception:  # pragma: no cover - comparator is optional at runtime
    sexpr_diff = None
    parse_sexpr = None


@dataclass
class RoundTripResult:
    path: str
    exit_match: Optional[bool]
    stdout_match: Optional[bool]
    stderr_match: Optional[bool]
    sexpr_ok: Optional[bool]
    details: Dict[str, object]


def run_cmd(cmd: List[str], cwd: Optional[Path] = None, timeout: int = 20) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        check=False,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def normalize_io(output: str) -> str:
    output = re.sub(r"/[^\s]+\.mg", "<FILE>", output)
    output = re.sub(r"\b\d+\b", "<NUM>", output)
    return output.strip()


def gather_inputs(paths: List[Path]) -> List[Path]:
    seen = set()
    inputs: List[Path] = []
    for path in paths:
        if path.is_dir():
            for file in sorted(path.rglob("*.mg")):
                if file not in seen:
                    inputs.append(file)
                    seen.add(file)
        elif path.suffix == ".mg" and path.exists():
            if path not in seen:
                inputs.append(path)
                seen.add(path)
    return inputs


def do_round_trip(src: Path, tmpdir: Path) -> Dict[str, Path]:
    metta_path = tmpdir / f"{src.stem}.metta"
    roundtrip_path = tmpdir / f"{src.stem}.roundtrip.mg"
    roundtrip_metta = tmpdir / f"{src.stem}.roundtrip.metta"

    mg_to_metta = run_cmd([sys.executable, str(MG_TO_METTA), str(src)])
    metta_path.write_text(mg_to_metta.stdout, encoding="utf-8")

    metta_to_mg = run_cmd([sys.executable, str(METTA_TO_MG), str(metta_path)])
    roundtrip_path.write_text(metta_to_mg.stdout, encoding="utf-8")

    rt_metta_proc = run_cmd([sys.executable, str(MG_TO_METTA), str(roundtrip_path)])
    roundtrip_metta.write_text(rt_metta_proc.stdout, encoding="utf-8")

    return {
        "metta": metta_path,
        "roundtrip_mg": roundtrip_path,
        "roundtrip_metta": roundtrip_metta,
        "logs": {
            "mg_to_metta": mg_to_metta,
            "metta_to_mg": metta_to_mg,
            "rt_metta_proc": rt_metta_proc,
        },
    }


def run_kernel(bin_path: Path, src: Path) -> subprocess.CompletedProcess:
    return run_cmd([str(bin_path), str(src)])


def compare_kernel_outputs(orig: subprocess.CompletedProcess, rt: subprocess.CompletedProcess) -> Dict[str, Optional[bool]]:
    o_stdout = normalize_io(orig.stdout)
    o_stderr = normalize_io(orig.stderr)
    r_stdout = normalize_io(rt.stdout)
    r_stderr = normalize_io(rt.stderr)
    return {
        "exit_match": orig.returncode == rt.returncode,
        "stdout_match": o_stdout == r_stdout,
        "stderr_match": o_stderr == r_stderr,
        "orig_exit": orig.returncode,
        "rt_exit": rt.returncode,
        "orig_stdout": o_stdout,
        "rt_stdout": r_stdout,
        "orig_stderr": o_stderr,
        "rt_stderr": r_stderr,
    }


def compare_sexprs(orig: Path, rt: Path) -> Dict[str, object]:
    if not parse_sexpr or not sexpr_diff:
        return {"sexpr_ok": None, "issues": ["compare_sexpr.py not available"]}
    orig_tree = parse_sexpr(orig.read_text(encoding="utf-8"))
    rt_tree = parse_sexpr(rt.read_text(encoding="utf-8"))
    issues = sexpr_diff(orig_tree, rt_tree)
    return {"sexpr_ok": not issues, "issues": issues}


def check_file(src: Path, megalodon_bin: Optional[Path], enable_kernel: bool, enable_sexpr: bool) -> RoundTripResult:
    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        artifacts = do_round_trip(src, tmpdir)

        detail: Dict[str, object] = {
            "metta": str(artifacts["metta"]),
            "roundtrip_mg": str(artifacts["roundtrip_mg"]),
            "roundtrip_metta": str(artifacts["roundtrip_metta"]),
        }

        exit_match = stdout_match = stderr_match = None
        if enable_kernel and megalodon_bin and megalodon_bin.exists():
            orig = run_kernel(megalodon_bin, src)
            rt = run_kernel(megalodon_bin, artifacts["roundtrip_mg"])
            kcmp = compare_kernel_outputs(orig, rt)
            detail["kernel"] = kcmp
            exit_match = kcmp["exit_match"]
            stdout_match = kcmp["stdout_match"]
            stderr_match = kcmp["stderr_match"]
        elif enable_kernel:
            detail["kernel"] = {"warning": f"Kernel binary not found at {megalodon_bin}"}

        sexpr_ok = None
        if enable_sexpr:
            sexpr_res = compare_sexprs(artifacts["metta"], artifacts["roundtrip_metta"])
            detail["sexpr"] = sexpr_res
            sexpr_ok = sexpr_res.get("sexpr_ok")

        return RoundTripResult(
            path=str(src),
            exit_match=exit_match,
            stdout_match=stdout_match,
            stderr_match=stderr_match,
            sexpr_ok=sexpr_ok,
            details=detail,
        )


def find_megalodon_bin(cli_path: Optional[Path]) -> Optional[Path]:
    """
    Resolve the Megalodon binary path with a forgiving search strategy:
      1) explicit CLI path if it exists
      2) MEGALODON_BIN env override
      3) walk up from this file to find megalodon/bin/megalodon
    """
    if cli_path and cli_path.exists():
        return cli_path

    env_path = os.environ.get("MEGALODON_BIN")
    if env_path:
        p = Path(env_path)
        if p.exists():
            return p

    for ancestor in BRIDGE_ROOT.parents:
        candidate = ancestor / "megalodon" / "bin" / "megalodon"
        if candidate.exists():
            return candidate

    return None


def main() -> None:
    parser = argparse.ArgumentParser(description="Round-trip Megalodon bridge harness.")
    parser.add_argument("paths", nargs="*", type=Path, help="Files or directories to test (defaults to valid_test.mg).")
    parser.add_argument("--include-fixtures", action="store_true", help="Include tests/fixtures/tactics/*.mg.")
    parser.add_argument("--include-examples", type=Path, help="Path to megalodon/examples to walk.")
    parser.add_argument("--include-fuzz", type=Path, help="Path to fuzz corpus (e.g., tests/fuzz).")
    parser.add_argument("--no-kernel", action="store_true", help="Skip Megalodon kernel executions.")
    parser.add_argument("--no-sexpr", action="store_true", help="Skip structural S-expression comparison.")
    parser.add_argument("--megalodon-bin", type=Path, default=None, help="Path to megalodon binary.")
    parser.add_argument("--report", type=Path, help="Optional JSON report path.")
    args = parser.parse_args()

    targets: List[Path] = []
    if args.paths:
        targets.extend(args.paths)
    else:
        targets.append(BRIDGE_ROOT / "valid_test.mg")

    if args.include_fixtures:
        targets.append(BRIDGE_ROOT / "tests" / "fixtures" / "tactics")
    if args.include_examples:
        targets.append(args.include_examples)
    if args.include_fuzz:
        targets.append(args.include_fuzz)

    inputs = gather_inputs(targets)
    if not inputs:
        print("No .mg files found to test.", file=sys.stderr)
        sys.exit(1)

    megalodon_bin = None if args.no_kernel else find_megalodon_bin(args.megalodon_bin)
    if not args.no_kernel:
        if megalodon_bin is None:
            print("Warning: Megalodon binary not found; set MEGALODON_BIN or use --megalodon-bin. Kernel checks will be skipped.", file=sys.stderr)
        else:
            print(f"Using Megalodon kernel: {megalodon_bin}")

    results = [
        check_file(
            src=i,
            megalodon_bin=megalodon_bin,
            enable_kernel=not args.no_kernel,
            enable_sexpr=not args.no_sexpr,
        )
        for i in inputs
    ]

    for res in results:
        print(f"{res.path}")
        print(f"  exit_match: {res.exit_match}  stdout_match: {res.stdout_match}  stderr_match: {res.stderr_match}  sexpr_ok: {res.sexpr_ok}")

    if args.report:
        payload = {"results": [asdict(r) for r in results]}
        args.report.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
