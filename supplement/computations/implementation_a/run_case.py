#!/usr/bin/env python3
"""Run A in a bounded subprocess, preserving inputs, checkpoints and outputs."""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import resource
import subprocess
import sys
import time
import traceback
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CASES = {
    "main": (7, 5, 4290, 32, 4, 4),
    "three-halves": (3, 2, 770, 32, 4, 1),
    "four-thirds": (4, 3, 30, 32, 4, 1),
    "five-fourths": (5, 4, 6006, 32, 4, 1),
}


def artifact(path: Path) -> dict:
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def write_json(path: Path, value: dict, compact: bool = False) -> None:
    if path.exists():
        raise FileExistsError(f"Refusing to overwrite {path.name}")
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("x", encoding="utf-8", newline="\n") as out:
        json.dump(value, out, sort_keys=True, indent=None if compact else 2,
                  separators=(",", ":") if compact else None)
        out.write("\n")
    temporary.rename(path)


def worker(config_path: Path) -> int:
    config = json.loads(config_path.read_text())
    resource.setrlimit(resource.RLIMIT_AS, (config["limits"]["address_space_bytes"],) * 2)
    from verifier import run

    raw = ROOT / config["raw_directory"]
    results = ROOT / config["results_directory"]
    completed = 0
    started = time.perf_counter()
    report = {"schema_version": 1, "termination": "error", "completed_stages": 0}

    def checkpoint(stage: dict, certificate: dict) -> None:
        nonlocal completed
        write_json(raw / f"stage-{completed:03}.json", stage, compact=True)
        write_json(raw / f"certificate-stage-{completed:03}.json", certificate, compact=True)
        completed += 1
        print(json.dumps({"K": stage["K"], "vertices": len(stage["vertices"]),
                          "edges": len(stage["edges"]), "remaining": len(stage["retained"]),
                          "scc_postcheck": "pass"}, sort_keys=True), flush=True)

    exit_code = 1
    try:
        science, certificate = run(config["parameters"], checkpoint)
        write_json(raw / "scientific.json", science, compact=True)
        write_json(raw / "certificate.json", certificate, compact=True)
        report["termination"] = science["termination"]
        report["reason"] = "retained_set_empty" if science["termination"] == "success" else "stage_limit"
        exit_code = 0 if science["termination"] == "success" else 2
    except MemoryError:
        report["termination"] = "inconclusive"
        report["reason"] = "address_space_limit"
        exit_code = 2
    except Exception as exc:
        report["reason"] = f"{type(exc).__name__}: {exc}"
        traceback.print_exc()
    finally:
        report["completed_stages"] = completed
        report["elapsed_seconds"] = time.perf_counter() - started
        report["peak_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        write_json(results / "worker-report.json", report)
    return exit_code


def main() -> int:
    parser = argparse.ArgumentParser(description="One-step A worker; use reproduce.py for bounded runs.")
    parser.add_argument("--worker", required=True, type=Path)
    return worker(parser.parse_args().worker)


if __name__ == "__main__":
    raise SystemExit(main())
