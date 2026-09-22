#!/usr/bin/env python3
"""Execution driver for implementation A (word-labelled method): bounded runs with records.

Each task runs one working copy of a supplied script (``scripts/``) in a fresh
directory under ``build/word-a/runs/<run-id>/`` with an address-space limit
and an outer timeout, then converts the scientific outputs into the normalized
text dumps (``computations/raw/<run-id>/``), copies the small outputs into
``computations/results/<run-id>/`` and writes ``run.json`` with the pre-run
record (hashes, versions, command, limits) and the post-run record (wall time,
exit code, termination, output hashes). Existing run ids are never overwritten.

Termination values: ``success`` = the script finished with exit code 0 and its
own result JSON does not report failure; ``inconclusive`` = a resource limit or
timeout was reached (the script's own INCONCLUSIVE, or the outer timeout);
``error`` = anything else. ``success`` here is the supplied script's own
verdict; the scientific meaning of each task is described in ../../COMPUTATION.md.

Usage: python3 run_word.py --task five-halves --date fresh --seq 01 [--skip-postcheck]
       python3 run_word.py --task five-halves --date fresh --seq 01 --redump --note '...'
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import resource
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent  # repository root
SCRIPTS = HERE / "scripts"
BUILD = ROOT / "build" / "word-a" / "runs"
RESULTS = ROOT / "computations" / "results"
RAW = ROOT / "computations" / "raw"
GIB = 1024 ** 3


@dataclass(frozen=True)
class Task:
    script: str
    origin: str               # path of the supplied original within the construction source set
    mode: str                 # workdir | output | output+witnesses | adjacent | output+workdir
    result: str               # name of the script's own result JSON
    timeout: int              # outer timeout in seconds (the driver kills the process group)
    address_space: int = 4 * GIB
    extra: tuple = ()
    dump: str = ""            # wordgraph | q75 | ""
    case: str = ""
    binaries: str = ""        # subdirectory of the generated work directory holding construction A's binaries
    scientific_limits_note: str = ""
    large: tuple = ()         # additional large outputs (relative to the work directory) moved to raw/


TASKS = {
    "five-halves": Task("verify_five_halves.py", "core/verify_five_halves.py", "workdir", "verification.json", 1500,
                        extra=("--keep-graphs",), dump="wordgraph", case="five-halves", binaries="raw_a",
                        scientific_limits_note="script default: 600 s and 4096 MiB address space per compiled subprocess (A and B each); outer 1500 s covers both"),
    "cross-75": Task("verify_cross_75.py", "core/verify_cross_75.py", "workdir", "cross_check.json", 300,
                     dump="wordgraph", case="cross-75", binaries="out_A",
                     scientific_limits_note="script hard-codes 120 s per compile and per binary; no memory limit of its own; outer 300 s / 4 GiB"),
    "q75": Task("verify_quantitative_75.py", "core/verify_quantitative_75.py", "output+workdir", "result.json", 300,
                dump="q75", scientific_limits_note="script hard-codes 60 s per compile and 120 s per binary; outer 300 s / 4 GiB"),
    "external-budget": Task("verify_external_budget.py", "core/verify_external_budget.py", "output", "result.json", 300,
                            scientific_limits_note="script has an internal interval-search cutoff of 100000 (raises inconclusive)"),
    "finite-height": Task("verify_finite_height.py", "appendix/verify_finite_height.py", "output+witnesses", "result.json", 300,
                          scientific_limits_note="C++ node cap 1e9 (exit 2 INCONCLUSIVE); 60 s compile, 180 s per enumeration",
                          large=("finite_height_witnesses.json",)),
    "sieve": Task("replay_sieve.py", "appendix/replay_sieve.py", "output", "result.json", 300,
                  scientific_limits_note="C++ node cap 1e9 (exit 2 INCONCLUSIVE); no subprocess timeout of its own"),
    "return-words": Task("verify_return_words.py", "appendix/verify_return_words.py", "adjacent", "verified_results.json", 300),
    "recurrence": Task("verify_recurrence.py", "appendix/verify_recurrence.py", "output", "result.json", 300),
    "reductions": Task("check_reductions.py", "appendix/check_reductions.py", "adjacent", "reduction_checks.json", 300),
}


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def file_record(path: Path, base: Path | None = None) -> dict:
    return dict(path=str(path.relative_to(base)) if base else str(path), bytes=path.stat().st_size, sha256=sha256_file(path))


def embedded_sources(script: Path) -> dict:
    """SHA-256 of every embedded C++ source string (SOURCE_* = '...')."""
    text = script.read_text(encoding="utf-8")
    out = {}
    for m in re.finditer(r"^(SOURCE_[A-Z_]+) = '(.*?)'\n", text, re.S | re.M):
        source = m.group(2).encode("utf-8").decode("unicode_escape")
        out[m.group(1)] = dict(sha256_decoded=hashlib.sha256(source.encode()).hexdigest(), bytes=len(source))
    return out


def environment() -> dict:
    gxx = subprocess.run(["g++", "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    mem = None
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemTotal"):
                mem = int(line.split()[1]) // 1024
    except OSError:
        pass
    return dict(python=sys.version, python_executable=sys.executable, gxx=gxx, platform=platform.platform(),
                cpu_count=os.cpu_count(), memtotal_mib=mem)


def run(task_name: str, date: str, seq: str, skip_postcheck: bool, source_sha256: str) -> int:
    task = TASKS[task_name]
    run_id = f"word-a-{task_name}-{date}-{seq}"
    results = RESULTS / run_id
    raw = RAW / run_id
    work = BUILD / run_id
    for d in (results, raw, work):
        if d.exists():
            raise SystemExit(f"{d} exists; choose a new run id")
    results.mkdir(parents=True)
    raw.mkdir(parents=True)
    work.mkdir(parents=True)
    script_src = SCRIPTS / task.script
    script = work / task.script
    shutil.copy2(script_src, script)
    original = script_src
    generated = work / "generated"
    command = [sys.executable, str(script)]
    result_path = work / task.result
    if task.mode == "workdir":
        command += ["--workdir", str(generated)]
        result_path = generated / task.result
    elif task.mode == "output+workdir":
        command += ["--output", str(result_path), "--workdir", str(generated)]
    elif task.mode == "output":
        command += ["--output", str(result_path)]
    elif task.mode == "output+witnesses":
        command += ["--output", str(result_path), "--witnesses", str(work / "finite_height_witnesses.json")]
    command += list(task.extra)
    record = dict(
        schema_version=2, run_id=run_id, task=task_name, implementation="A (word-labelled method; working copy of the supplied construction)",
        independent_verification=False, source_sha256=source_sha256,
        pre_run=dict(recorded_at=now(),
                     script=dict(working_copy=file_record(script_src, ROOT), distributed_source=file_record(original, ROOT),
                                 identical_to_distributed=sha256_file(script_src) == sha256_file(original),
                                 embedded_cxx_sources=embedded_sources(script_src)),
                     environment=environment(), command=command, cwd=str(work),
                     limits=dict(outer_timeout_seconds=task.timeout, address_space_bytes=task.address_space,
                                 address_space_note="RLIMIT_AS applied to the script process and inherited by g++ and the compiled programs",
                                 script_own_limits=task.scientific_limits_note)),
    )
    (results / "run.json").write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    def limits() -> None:
        resource.setrlimit(resource.RLIMIT_AS, (task.address_space, task.address_space))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    start = time.monotonic()
    started_at = now()
    termination, reason, code = "error", "", None
    with (results / "stdout.log").open("wb") as out, (results / "stderr.log").open("wb") as err:
        proc = subprocess.Popen(command, cwd=work, stdout=out, stderr=err, preexec_fn=limits, start_new_session=True)
        try:
            code = proc.wait(timeout=task.timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            termination, reason = "inconclusive", f"outer timeout {task.timeout} s reached; process group killed"
    wall = time.monotonic() - start
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    stderr_text = (results / "stderr.log").read_text(errors="replace")
    result_data = None
    if code == 0 and result_path.is_file():
        result_data = json.loads(result_path.read_text(encoding="utf-8"))
        failed = isinstance(result_data, dict) and (result_data.get("success") is False or result_data.get("all_full_graphs_equal") is False)
        if failed:
            termination, reason = "error", "result JSON reports failure"
        else:
            termination, reason = "success", "script exit code 0 and its result JSON present"
    elif code == 0:
        termination, reason = "error", "exit code 0 but the result JSON is missing"
    elif code is not None:
        if "INCONCLUSIVE" in stderr_text or "inconclusive" in stderr_text.lower():
            termination, reason = "inconclusive", f"exit code {code}; script reported INCONCLUSIVE"
        else:
            termination, reason = "error", f"exit code {code}"
    outputs = []
    if result_path.is_file():
        dest = results / ("script-result-" + task.result)
        shutil.copy2(result_path, dest)
        outputs.append(file_record(dest, ROOT))
    for name in ("run_a.jsonl", "run_b.jsonl", "run_a.err", "run_b.err", "run_A.jsonl", "run_B.jsonl",
                 "construction_a.cpp", "construction_b.cpp", "cross_A.cpp", "cross_B.cpp", "graph_a.cpp", "graph_b.cpp",
                 "failure.json"):
        p = generated / name if (generated / name).is_file() else work / name
        if p.is_file():
            dest = results / name
            shutil.copy2(p, dest)
            outputs.append(file_record(dest, ROOT))
    raw_outputs = []
    for name in task.large:
        p = work / name
        if p.is_file():
            dest = raw / name
            shutil.copy2(p, dest)
            raw_outputs.append(file_record(dest, ROOT))
    # the supplied binaries of construction A and B, hashed (kept in raw/)
    for sub in ("raw_a", "raw_b", "out_A", "out_B"):
        d = generated / sub
        if d.is_dir():
            for p in sorted(d.iterdir()):
                dest = raw / sub / p.name
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(p, dest)
                raw_outputs.append(file_record(dest, ROOT))
    if task.mode == "output+workdir" and generated.is_dir():
        for p in sorted(generated.glob("graph*_*.bin")):
            dest = raw / "arrays" / p.name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(p, dest)
            raw_outputs.append(file_record(dest, ROOT))
    record["post_run"] = dict(started_at=started_at, finished_at=now(), wall_seconds=round(wall, 3), exit_code=code,
                              termination=termination, termination_reason=reason,
                              children_ru_maxrss_kib=usage.ru_maxrss, children_utime_seconds=usage.ru_utime,
                              note="wall time is the parent's wait; ru_maxrss is the largest waited descendant as reported by Linux; both are observations, not requirements")
    record["outputs"] = outputs
    record["raw_outputs"] = raw_outputs
    (results / "run.json").write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(record["post_run"]), flush=True)
    if termination != "success":
        return 2
    dump_and_postcheck(task, record, results, raw, generated, skip_postcheck)
    record["results_files"] = [file_record(p, ROOT) for p in sorted(results.rglob("*")) if p.is_file() and p.name != "run.json"]
    if not any(raw.iterdir()):
        raw.rmdir()
        record["raw_directory"] = "none (no large output)"
    (results / "run.json").write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


def dump_and_postcheck(task: Task, record: dict, results: Path, raw: Path, generated: Path, skip_postcheck: bool) -> None:
    """Convert construction A's binaries into the normalized text dumps and run the A-side postchecks."""
    dumps = []
    dump_dir = raw / "dumps"
    if dump_dir.exists():
        shutil.rmtree(dump_dir)
    excerpts = results / "excerpts"
    if excerpts.exists():
        shutil.rmtree(excerpts)
    for stale in ("dump-manifest.json", "postcheck.json", "postcheck.log"):
        if (results / stale).exists():
            (results / stale).unlink()
    if task.dump == "wordgraph":
        binaries = generated / task.binaries
        t0 = time.monotonic()
        subprocess.run([sys.executable, str(HERE / "dump_wordgraph.py"), "--case", task.case, "--binaries", str(binaries),
                        "--out", str(dump_dir), "--manifest", str(results / "dump-manifest.json")], check=True)
        record["dump"] = dict(format="WORDGRAPH 2", seconds=round(time.monotonic() - t0, 3), binaries=str(binaries.relative_to(ROOT)))
        excerpts.mkdir()
        for p in sorted(dump_dir.iterdir()):
            dumps.append(file_record(p, ROOT))
            if p.stat().st_size <= 65536:
                shutil.copy2(p, excerpts / p.name)
        if not skip_postcheck:
            candidates = [generated / "run_a.jsonl", generated / "run_A.jsonl", results / "run_a.jsonl", results / "run_A.jsonl"]
            summary = next(c for c in candidates if c.exists())
            t0 = time.monotonic()
            pc = subprocess.run([sys.executable, str(HERE / "postcheck_wordgraph.py"), "--case", task.case, "--dumps", str(dump_dir),
                                 "--summary", str(summary), "--out", str(results / "postcheck.json")], capture_output=True, text=True)
            (results / "postcheck.log").write_text(pc.stdout + pc.stderr, encoding="utf-8")
            record["postcheck"] = dict(exit_code=pc.returncode, seconds=round(time.monotonic() - t0, 3), report="postcheck.json",
                                       passed=pc.returncode == 0)
    elif task.dump == "q75":
        t0 = time.monotonic()
        subprocess.run([sys.executable, str(HERE / "dump_q75.py"), "--prefix", str(generated / "graphA"), "--out", str(dump_dir),
                        "--manifest", str(results / "dump-manifest.json")], check=True)
        record["dump"] = dict(format="Q75GRAPH 2", seconds=round(time.monotonic() - t0, 3), arrays=str((generated / "graphA_edges.bin").parent.relative_to(ROOT)))
        excerpts.mkdir()
        for p in sorted(dump_dir.iterdir()):
            dumps.append(file_record(p, ROOT))
        shutil.copy2(dump_dir / "q75-cyclic-blocks-excerpt.txt", excerpts / "q75-cyclic-blocks-excerpt.txt")
        if not skip_postcheck:
            t0 = time.monotonic()
            pc = subprocess.run([sys.executable, str(HERE / "postcheck_q75.py"), "--dumps", str(dump_dir),
                                 "--out", str(results / "postcheck.json")], capture_output=True, text=True)
            (results / "postcheck.log").write_text(pc.stdout + pc.stderr, encoding="utf-8")
            record["postcheck"] = dict(exit_code=pc.returncode, seconds=round(time.monotonic() - t0, 3), report="postcheck.json",
                                       passed=pc.returncode == 0)
    record["normalized_dumps"] = dumps


def redump(task_name: str, date: str, seq: str, skip_postcheck: bool, note: str) -> int:
    """Regenerate the normalized dumps and postchecks of an existing run from its preserved binaries.

    The computation itself is not repeated: the binaries copied into
    computations/raw/<run-id>/ by the original run are used. The run record
    keeps its pre-run and post-run sections and gains a ``redump`` entry.
    """
    task = TASKS[task_name]
    run_id = f"word-a-{task_name}-{date}-{seq}"
    results = RESULTS / run_id
    raw = RAW / run_id
    record = json.loads((results / "run.json").read_text(encoding="utf-8"))
    if record["post_run"]["termination"] != "success":
        raise SystemExit("redump refuses a run that did not terminate successfully")
    if task.dump == "wordgraph":
        generated = raw  # raw/<run-id>/raw_a or out_A hold the preserved binaries
    else:
        generated = raw / "arrays"
    for entry in record.get("raw_outputs", []):
        p = ROOT / entry["path"]
        if not p.is_file() or sha256_file(p) != entry["sha256"]:
            raise SystemExit(f"preserved binary changed or missing: {entry['path']}")
    dump_and_postcheck(task, record, results, raw, generated, skip_postcheck)
    record.setdefault("redump_history", []).append(dict(at=now(), note=note, python=sys.version.split()[0],
                                                       tools_sha256={n: sha256_file(HERE / n) for n in ("wg_format.py", "dump_wordgraph.py", "dump_q75.py", "postcheck_wordgraph.py", "postcheck_q75.py")}))
    record["results_files"] = [file_record(p, ROOT) for p in sorted(results.rglob("*")) if p.is_file() and p.name != "run.json"]
    (results / "run.json").write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(dict(run_id=run_id, dump=record.get("dump"), postcheck=record.get("postcheck"))))
    return 0 if record.get("postcheck", {}).get("passed", True) else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", choices=sorted(TASKS), required=True)
    parser.add_argument("--date", required=True)
    parser.add_argument("--seq", default="01")
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--skip-postcheck", action="store_true")
    parser.add_argument("--redump", action="store_true", help="regenerate dumps/postchecks of an existing run from its preserved binaries")
    parser.add_argument("--note", default="", help="reason recorded with --redump")
    args = parser.parse_args()
    if args.redump:
        return redump(args.task, args.date, args.seq, args.skip_postcheck, args.note)
    return run(args.task, args.date, args.seq, args.skip_postcheck, args.source_sha256)


if __name__ == "__main__":
    raise SystemExit(main())
