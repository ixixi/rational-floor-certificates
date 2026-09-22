#!/usr/bin/env python3
"""Verify this distribution and reproduce its independent integer computations."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import signal
import subprocess
import sys
import time

PACKET = Path(__file__).resolve().parent
SCIENCE = PACKET / "supplement"
CASES = ("main", "three-halves", "four-thirds", "five-fourths")


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")


def verify():
    manifest_path = PACKET / "MANIFEST.json"
    manifest = json.loads(manifest_path.read_text())
    rows = manifest["files"]
    names = [entry["path"] for entry in rows]
    if len(names) != len(set(names)):
        raise ValueError("Manifest paths must be unique")
    for entry in rows:
        relative = Path(entry["path"])
        path = PACKET / relative
        if relative.is_absolute() or ".." in relative.parts or not path.resolve().is_relative_to(PACKET):
            raise ValueError("Manifest path escapes the repository")
        if not path.is_file() or path.stat().st_size != entry["bytes"] or sha(path) != entry["sha256"]:
            raise ValueError(f"Distribution file differs: {entry['path']}")
    source_rows = [row for row in rows if not row["path"].endswith(".pdf")]
    encoded = json.dumps(source_rows, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    if hashlib.sha256(encoded).hexdigest() != manifest["source_sha256"]:
        raise ValueError("Source content digest differs")
    expected = set(names) | {"MANIFEST.json", "SHA256SUMS"}
    ignored_directories = {"__pycache__", ".pytest_cache", ".mypy_cache", ".ruff_cache", ".lake"}
    actual = set()
    ignored = []
    for directory, dirs, files in os.walk(PACKET):
        relative = Path(directory).relative_to(PACKET)
        for name in list(dirs):
            if name in ignored_directories or (not relative.parts and name in (".git", "build")):
                ignored.append((relative / name).as_posix() + "/")
                dirs.remove(name)
        for name in files:
            path = (relative / name).as_posix()
            if path not in expected and (name.endswith((".pyc", ".pyo")) or name == ".DS_Store" or path == ".git"):
                ignored.append(path)
                continue
            actual.add(path)
    if actual != expected:
        raise ValueError(f"Distribution file set differs: {sorted(actual ^ expected)}")
    checksums = {}
    for line in (PACKET / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        if name in checksums:
            raise ValueError("Repeated checksum path")
        checksums[name] = digest
    if set(checksums) != set(names) | {"MANIFEST.json"}:
        raise ValueError("Incomplete checksum index")
    for name, digest in checksums.items():
        if sha(PACKET / name) != digest:
            raise ValueError(f"Checksum differs: {name}")
    return {"status": "PASS", "files": len(expected), "manifest_sha256": sha(manifest_path),
            "source_sha256": manifest["source_sha256"], "ignored_runtime_paths": sorted(ignored)}


def bounded(command, output, name, seconds, memory, cwd=None):
    cwd = SCIENCE if cwd is None else Path(cwd)
    hard_limit = resource.getrlimit(resource.RLIMIT_AS)[1]
    if hard_limit != resource.RLIM_INFINITY:
        memory = min(memory, hard_limit)
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
    start = time.monotonic()
    stdout, stderr = output / f"{name}.stdout.log", output / f"{name}.stderr.log"
    with stdout.open("xb") as out, stderr.open("xb") as err:
        process = subprocess.Popen(command, cwd=cwd, stdout=out, stderr=err,
                                   env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                                   preexec_fn=limits, start_new_session=True)
        timeout = False
        try:
            process.wait(timeout=seconds)
        except subprocess.TimeoutExpired:
            timeout = True
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
    inconclusive = timeout or process.returncode < 0 or "MemoryError" in stderr.read_text(errors="replace")
    return {"command": [str(x) for x in command], "cwd": str(cwd),
            "limits": {"wall_seconds": seconds, "address_space_bytes": memory},
            "exit_code": process.returncode, "elapsed_seconds": time.monotonic() - start,
            "status": "inconclusive" if inconclusive else "PASS" if process.returncode == 0 else "FAIL",
            "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr)}




def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("verify", "check", "recompute"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
        parser.error("Keep Python assertions enabled")
    identity = verify()
    if args.mode == "verify":
        print(json.dumps(identity))
        return
    if args.output is None:
        parser.error("--output is required and must be a fresh directory outside the distribution")
    output = args.output.resolve()
    if output.is_relative_to(PACKET) or PACKET.is_relative_to(output):
        parser.error("Use an output directory outside the distribution")
    output.mkdir(parents=True, exist_ok=False)
    record = {"schema_version": 1, "mode": args.mode, "python": platform.python_version(),
              "platform": platform.platform(), "input_verification": identity,
              "commands": [], "status": "running"}
    dump(output / "record.json", record)
    python = [sys.executable, "-B"]
    commands = [
        (python + [str(PACKET / "replay.py"), "run", "--scope",
                   "full" if args.mode == "recompute" else "preflight",
                   "--out", str(output / "finite"), "--command-seconds", "600",
                   "--total-seconds", "1800", "--memory-gib", "8"],
         "finite-replay", 1860, 8 << 30),
    ]
    try:
        for command, name, seconds, memory in commands:
            result = bounded(command, output, name, seconds, memory)
            # The child reports its own resource stops before exiting nonzero.
            # Preserve that boundary instead of labelling it a failed result.
            receipt = output / "finite/receipt.json"
            if receipt.is_file():
                try:
                    child_status = json.loads(receipt.read_text()).get("status")
                except (OSError, ValueError):
                    child_status = None
                result["child_receipt_status"] = child_status
                if child_status == "inconclusive":
                    result["status"] = "inconclusive"
            record["commands"].append(result)
            dump(output / "record.json", record)
            print(json.dumps({"step": name, "status": result["status"]}), flush=True)
            if result["status"] != "PASS":
                record["status"] = result["status"]
                raise RuntimeError(f"{name}: {result['status']}")
        record["status"] = "PASS"
        record["inputs_unchanged"] = verify()
    except Exception as error:
        if record["status"] == "running":
            record["status"] = "FAIL"
        record["error"] = str(error)
        raise
    finally:
        record["outputs"] = [{"path": p.relative_to(output).as_posix(), "bytes": p.stat().st_size,
                              "sha256": sha(p)} for p in sorted(output.rglob("*"))
                             if p.is_file() and p.name != "record.json"]
        dump(output / "record.json", record)


if __name__ == "__main__":
    main()
