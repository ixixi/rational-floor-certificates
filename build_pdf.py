#!/usr/bin/env python3
"""Build an English or Japanese PDF from the distributed TeX source."""
from __future__ import annotations

import argparse
import json
import hashlib
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import tempfile
import time

from pdf_links import relocate
from tex_diagnostics import diagnostic_lines

ROOT = Path(__file__).resolve().parent
EPOCH = 1790034213


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--language", choices=("en", "ja"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        parser.error("Use an output filename outside the distribution")
    if output.exists() or output.with_suffix(".build.json").exists():
        parser.error("Choose a fresh output filename")
    logs = output.with_suffix(".build-logs")
    logs.mkdir(parents=True, exist_ok=False)
    source_name = "paper.tex" if args.language == "en" else "paper-ja.tex"
    engine = "pdflatex" if args.language == "en" else "lualatex"
    source = ROOT / "sources" / source_name
    output.parent.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "SOURCE_DATE_EPOCH": str(EPOCH), "FORCE_SOURCE_DATE": "1", "TZ": "UTC"}
    record = {"status": "running", "language": args.language, "engine": engine,
              "source_date_epoch": EPOCH,
              "limits": {"wall_seconds": 600, "address_space_bytes": 4 << 30, "passes": 10},
              "commands": []}
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
    start = time.monotonic()
    try:
        with tempfile.TemporaryDirectory(prefix="floor-paper-tex-") as directory:
            work = Path(directory)
            shutil.copyfile(source, work / source_name)
            # The figure fragments are publication sources, shared by both languages.
            figures = ROOT / "sources" / "figures"
            if figures.exists():
                shutil.copytree(figures, work / "figures")
            previous = None
            for iteration in range(10):
                command = [engine, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", source_name]
                remaining = 600 - (time.monotonic() - start)
                if remaining <= 0:
                    record["status"] = "inconclusive"
                    raise TimeoutError("Total TeX build deadline")
                timed_out = False
                with (work / f"pass-{iteration+1}.log").open("wb") as log:
                    process = subprocess.Popen(command, cwd=work, env=env, stdout=log,
                                               stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=limits)
                    try:
                        process.wait(timeout=remaining)
                    except subprocess.TimeoutExpired:
                        timed_out = True
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
                        record["status"] = "inconclusive"
                saved_log = logs / f"pass-{iteration+1:02d}.stdout.log"
                shutil.copyfile(work / f"pass-{iteration+1}.log", saved_log)
                record["commands"].append({"command": command, "exit_code": process.returncode,
                                           "stdout": str(saved_log),
                                           "stdout_sha256": hashlib.sha256(saved_log.read_bytes()).hexdigest()})
                if timed_out:
                    raise TimeoutError("TeX process wall limit reached; partial log retained")
                if process.returncode:
                    record["last_log"] = (work / f"pass-{iteration+1}.log").read_text(errors="replace")
                    if process.returncode < 0 or any(marker in record["last_log"] for marker in
                            ("MemoryError", "Cannot allocate memory", "not enough memory",
                             "out of memory", "TeX capacity exceeded", "bad_alloc")):
                        record["status"] = "inconclusive"
                    raise RuntimeError(f"{engine} exited {process.returncode}")
                stem = Path(source_name).stem
                current = {suffix: (work / (stem + suffix)).read_bytes()
                           for suffix in (".aux", ".out", ".toc") if (work / (stem + suffix)).exists()}
                if current == previous:
                    final_log = work / (stem + ".log")
                    shutil.copyfile(final_log, logs / "final.log")
                    record["warnings"] = diagnostic_lines(final_log.read_text(errors="replace"))
                    if record["warnings"]:
                        raise RuntimeError("Final TeX diagnostics remain; inspect retained logs")
                    record["relocation"] = relocate(work / (stem + ".pdf"), output, ROOT)
                    record["status"] = "PASS"
                    break
                previous = current
            else:
                record["status"] = "inconclusive"
                raise RuntimeError("TeX references did not stabilize in 10 passes")
    except Exception as error:
        if record["status"] == "running":
            record["status"] = "FAIL"
        record["error"] = str(error)
        raise
    finally:
        record["elapsed_seconds"] = time.monotonic() - start
        output.with_suffix(".build.json").write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": "PASS", "output": str(output)}))


if __name__ == "__main__":
    main()
