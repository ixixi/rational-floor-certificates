#!/usr/bin/env python3
"""Reproduce the audited 5/3 certificate, or its separate small reference check.

Requires Python >= 3.9 and g++ supporting C++17. The full run is CPU/memory
intensive: this release's recorded run peaked at approximately 2.54 GiB RSS.
Run only one full instance at a time. Resource exhaustion is never success.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
PRIMES = "7,11,13,17,19,23,29,31,37"
SCIENTIFIC_FIELDS = (
    "p", "vin", "ein", "cyclic", "certified", "retained",
    "vout", "eout", "letters", "maxlen",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def verify_manifest() -> None:
    """File identification/integrity only, not mathematical verification."""
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        digest, relative = line.split("  ", 1)
        path = ROOT / relative
        require(path.is_file(), f"Missing distributed file: {relative}")
        found = hashlib.sha256(path.read_bytes()).hexdigest()
        require(found == digest, f"Source/data hash mismatch: {relative}")


def execute(command: list[str], output: Path, error: Path,
            timeout: int, env: dict[str, str]) -> dict:
    started = time.monotonic()
    with output.open("w") as stdout, error.open("w") as stderr:
        try:
            result = subprocess.run(command, stdout=stdout, stderr=stderr,
                                    timeout=timeout, env=env, check=False)
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(f"Time limit reached; inconclusive. See {output}.") from exc
    require(result.returncode == 0,
            f"Process exited {result.returncode}; not accepted. See {error}.")
    try:
        data = json.loads(output.read_text())
    except (OSError, ValueError) as exc:
        raise RuntimeError(f"Incomplete or invalid output: {output}") from exc
    data["replay_elapsed_seconds"] = time.monotonic() - started
    return data


def compare_stages(actual: dict, expected: dict) -> None:
    for key in ("a", "b", "K", "D", "bidir", "splits"):
        require(actual.get(key) == expected.get(key), f"Parameter mismatch: {key}")
    require(len(actual["stages"]) == len(expected["stages"]), "Stage count mismatch")
    for i, (left, right) in enumerate(zip(actual["stages"], expected["stages"])):
        for key in SCIENTIFIC_FIELDS:
            require(left[key] == right[key], f"Stage {i} mismatch: {key}")
    # Counts are reproducibility checks. Mathematical acceptance is provided by
    # the all-edge/all-letter checker that ran inside the C++ calculation.
    require(actual["audit"] == expected["audit"], "Audit coverage count mismatch")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("full", "small", "all"), nargs="?", default="all")
    parser.add_argument("--out", type=Path, default=ROOT / "replay")
    parser.add_argument("--timeout", type=int, default=1800)
    parser.add_argument("--compiler", default="g++")
    args = parser.parse_args()
    require(args.timeout > 0, "The time limit must be positive")
    verify_manifest()
    compiler = shutil.which(args.compiler)
    require(compiler is not None, f"C++ compiler not found: {args.compiler}")
    out = args.out.resolve()
    require(not out.exists(), f"Output directory already exists: {out}; choose a new path.")
    out.mkdir(parents=True)
    exe = out / "certificate53"
    subprocess.run([compiler, "-O3", "-std=c++17", str(ROOT / "certificate53.cpp"),
                    "-o", str(exe)], check=True, timeout=120)
    env = os.environ.copy()
    env["BIDIR"] = "1"
    report: dict = {"mode": args.mode, "acceptance": "not_yet_accepted"}
    if args.mode in ("small", "all"):
        folder = out / "small"
        folder.mkdir()
        small = execute([str(exe), "5", "3", "3", "7,11,13,17", "100000",
                         str(folder / "graph")], folder / "cpp_result.json",
                        folder / "cpp_stderr.txt", args.timeout, env)
        require(small.get("status") == "budget_exhausted",
                "Unexpected small-run status; the small run is not the full theorem.")
        expected = json.loads((ROOT / "recorded/small/cpp_result.json").read_text())
        compare_stages(small, expected)
        reference = execute([sys.executable, str(ROOT / "reference53.py"), "--compare",
                             str(folder), "--output", str(folder / "python_result.json")],
                            folder / "python_stdout.json", folder / "python_stderr.txt",
                            args.timeout, env)
        require(reference.get("status") == "all_elements_match", "Reference check failed")
        for key, value in (("compared_graphs", 10), ("vertices", 5834),
                           ("edges", 13260), ("letters", 52757)):
            require(reference[key] == value, f"Reference coverage mismatch: {key}")
        report["small"] = reference
    if args.mode in ("full", "all"):
        full = execute([str(exe), "5", "3", "3", PRIMES, "25000000"],
                       out / "full_result.json", out / "full_stderr.txt", args.timeout, env)
        require(full.get("status") == "success", f"Full run did not certify: {full.get('status')}")
        expected = json.loads((ROOT / "recorded/full_result.json").read_text())
        compare_stages(full, expected)
        last = full["stages"][-1]
        require(last["p"] == 37 and last["retained"] == last["vout"] == last["eout"] == 0,
                "Final graph is not empty")
        require(last["cyclic"] == last["certified"] == 14920,
                "Final all-component certification mismatch")
        require(full["audit"]["interval_edges"] == full["audit"]["geometry"] == 0,
                "Unexpected interval pruning")
        report["full"] = full
    report["acceptance"] = "requested_checks_passed"
    (out / "replay_report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError) as exc:
        print(f"NOT ACCEPTED: {exc}", file=sys.stderr)
        sys.exit(1)
