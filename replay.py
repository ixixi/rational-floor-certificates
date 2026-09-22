#!/usr/bin/env python3
"""Bounded replay of the independent integer computations.

No graph, SCC, certification, sieve, or mathematical algorithm is implemented
here. The only imported scientific module is the existing appendix comparator;
its path constants are rebound in the private workspace, never in the source.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import sys
import time

PUBLIC = Path(__file__).resolve().parent
ROOT = PUBLIC / "supplement"
STEP_CASES = ("main", "three-halves", "four-thirds", "five-fourths")
A_APPENDIX = ("external-budget", "finite-height", "sieve", "return-words", "recurrence", "reductions")
RESULT_NAMES = {"return-words": "verified_results.json", "reductions": "reduction_checks.json"}
B_FIRST = ("b01_obr_witness", "b02_interval", "b03_coding", "b04_residues",
           "b05_jacobsthal", "b06_contrapositive", "b07_effective_bound",
           "b08_no_external", "b09_cut_t", "b10_geo", "b11_ob_m",
           "b12_dom_languages", "b13_projection", "b14_numbers")
B_REST = ("f1_sieve", "f1_oracle", "f2_candidates", "f3_small_primes",
          "c1_sieve_constants", "r1_rec_fin", "r2_rec_digit", "r3_example",
          "n1_nb", "n2_nb_stop", "n3_nb_fork", "n4_nb_gap", "l1_long_prefix",
          "w1_return_words", "w2_return17")
APPENDIX_KEYS = dict(zip(
    ("b02", "b09", "b14", "f1", "f1o", "f2a", "f2b", "f3", "c1",
     "r1", "r2", "r3", "n1", "n2", "n3", "n4", "l1", "w1", "w2"),
    ("b02_interval", "b09_cut_t", "b14_numbers", "f1_sieve", "f1_oracle",
     "f2_candidates", "f2_candidates_10000", "f3_small_primes", "c1_sieve_constants",
     "r1_rec_fin", "r2_rec_digit", "r3_example", "n1_nb", "n2_nb_stop",
     "n3_nb_fork", "n4_nb_gap", "l1_long_prefix", "w1_return_words", "w2_return17")))
GRAPH_ARGS = {
    "five-halves": ["pipeline", "--a", "5", "--b", "2", "--K", "4", "--carries", "-1,1,3",
                    "--primes", "3,7,11,13,17,19,23,29,31"],
    "cross-75": ["pipeline", "--a", "7", "--b", "5", "--K", "2048", "--carries", "-4,-2,2,4,6",
                 "--primes", "3,11,13"],
    "q75": ["q75", "--a", "7", "--b", "5", "--M", "429", "--K", "2048",
            "--carries", "-4,-2,2,4,6"],
}
# Exact field names, not a general rule dropping time/hash/false-valued fields.
# Summary prose is redundant with the retained structured results; f1 includes
# elapsed time there. Compiler/binary identity is provenance, not mathematics.
B_OPERATIONAL_KEYS = {"elapsed_seconds", "binary_sha256", "compiler", "summary"}


def now():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n")


def strip_operational(value, omitted, where="$", keys=frozenset()):
    if isinstance(value, dict):
        result = {}
        for key, item in value.items():
            loc = where + "." + key
            if key in keys:
                omitted.append({"field": loc, "value": item})
            else:
                result[key] = strip_operational(item, omitted, loc, keys)
        return result
    if isinstance(value, list):
        return [strip_operational(v, omitted, f"{where}[{i}]", keys) for i, v in enumerate(value)]
    return value


def compare_json(actual, expected, output, keys=frozenset()):
    omit_a, omit_b = [], []
    a = strip_operational(read(actual), omit_a, keys=keys)
    b = strip_operational(read(expected), omit_b, keys=keys)
    same = a == b
    save(output, {"status": "PASS" if same else "MISMATCH", "actual": str(actual),
                  "expected": str(expected), "actual_sha256": digest(actual),
                  "expected_sha256": digest(expected), "equal_complete_structured_content": same,
                  "omitted_actual": omit_a, "omitted_expected": omit_b})
    if not same:
        raise ValueError(f"Structured scientific output differs: {actual}")


def proc_table():
    rows = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            words = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            rows[int(entry.name)] = (int(words[1]), int(words[21]) * os.sysconf("SC_PAGE_SIZE"))
        except (OSError, ValueError, IndexError):
            pass
    return rows


def descendants(table, root):
    found = {root}
    while True:
        new = {pid for pid, (parent, _) in table.items() if parent in found}
        if new <= found:
            return found
        found |= new


class Replay:
    def __init__(self, args):
        self.args = args
        self.out = args.out.resolve()
        if self.out.exists():
            raise ValueError("Output exists; choose a fresh --out (never overwrite a run)")
        if self.out.is_relative_to(PUBLIC) or PUBLIC.is_relative_to(self.out):
            raise ValueError("Output must not contain the source checkout")
        self.out.mkdir(parents=True)
        self.work = self.out / "workspace"
        self.refs = self.out / "references"
        self.work.mkdir()
        self.started = time.monotonic()
        self.steps = []
        self.inputs = []
        self.b_runs = {}
        self.record = {"schema_version": 1, "scope": args.scope, "status": "running",
                       "started_at": now(), "source_checkout": str(ROOT),
                       "source_sha256": read(PUBLIC / "MANIFEST.json")["source_sha256"],
                       "limits": {"per_command_seconds": args.command_seconds,
                                  "total_seconds": args.total_seconds, "memory_gib": args.memory_gib},
                       "no_old_raw_or_build_copied": True, "steps": self.steps}
        self.write_receipt()

    def write_receipt(self):
        save(self.out / "receipt.json", self.record)

    def copy(self, relative, reference=False):
        src = (PUBLIC if reference else ROOT) / relative
        dst = (self.refs if reference else self.work) / relative
        if dst.exists():
            return
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        self.inputs.append({"path": str(relative) if reference else "supplement/" + str(relative),
                            "copy_path": str(relative), "reference_only": reference,
                            "bytes": src.stat().st_size, "sha256": digest(src)})

    def snapshot(self):
        for folder in ("computations/implementation_a", "computations/implementation_b",
                       "computations/word_a", "computations/word_b"):
            for p in sorted((ROOT / folder).rglob("*")):
                if p.is_file() and "__pycache__" not in p.parts and p.suffix in (".py", ".cpp", ".h"):
                    self.copy(p.relative_to(ROOT))
        for name in ("main-stages.csv", "periodic-components.csv", "known-cases.csv"):
            self.copy(Path("evidence/expected") / name)
        self.copy(Path("checks/reference.json"), reference=True)
        self.reference = read(self.refs / "checks/reference.json")
        for kind in ("a", "b"):
            for name, result in self.reference["appendix_" + kind].items():
                save(self.refs / ("appendix-" + kind) / (name + ".json"), result)
        expected = dict(self.reference["appendix_comparison"], date=None, inputs_sha256={})
        save(self.refs / "appendix-comparison.json", expected)
        (self.work / "build/word-appendix").mkdir(parents=True)
        (self.work / "build/word-replay").mkdir(parents=True)
        save(self.out / "inputs.json", {"source_sha256": self.record["source_sha256"], "files": self.inputs})
        if (self.work / "computations/raw").exists():
            raise ValueError("Workspace unexpectedly has old raw data")

    def run(self, name, command, environment=None):
        remaining = self.args.total_seconds - (time.monotonic() - self.started)
        if remaining <= 0:
            self.record["status"] = "inconclusive"
            raise TimeoutError("Total replay time limit reached")
        budget = min(self.args.command_seconds, remaining)
        directory = self.out / "commands" / f"{len(self.steps):03}-{name}"
        directory.mkdir(parents=True)
        row = {"name": name, "command": [str(s) for s in command], "cwd": str(self.work),
               "started_at": now(), "wall_limit_seconds": budget, "status": "running",
               "stdout": str(directory / "stdout.log"), "stderr": str(directory / "stderr.log")}
        self.steps.append(row)
        self.write_receipt()
        cap = self.args.memory_gib * (1 << 30)

        def limits():
            resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

        before = time.monotonic()
        peak, stop = 0, None
        env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1", "TMPDIR": str(self.work / "build/word-replay"), **(environment or {})}
        with (directory / "stdout.log").open("wb") as stdout, (directory / "stderr.log").open("wb") as stderr:
            process = subprocess.Popen(row["command"], cwd=self.work, stdout=stdout, stderr=stderr,
                                       env=env, preexec_fn=limits, start_new_session=True)
            try:
                while process.poll() is None:
                    table = proc_table()
                    ids = descendants(table, process.pid)
                    rss = sum(table.get(pid, (0, 0))[1] for pid in ids)
                    peak = max(peak, rss)
                    if time.monotonic() - before > budget:
                        stop = "wall-clock limit"
                    elif rss > cap:
                        stop = "sampled descendant RSS limit"
                    if stop:
                        for pid in sorted(ids, reverse=True):
                            try:
                                os.kill(pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                        break
                    time.sleep(0.1)
                code = process.wait()
            except BaseException:
                for pid in descendants(proc_table(), process.pid):
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                process.wait()
                raise
        row.update(finished_at=now(), elapsed_seconds=round(time.monotonic() - before, 3),
                   exit_code=code, peak_sampled_descendant_rss_bytes=peak,
                   stdout_sha256=digest(directory / "stdout.log"), stderr_sha256=digest(directory / "stderr.log"))
        error_text = (directory / "stderr.log").read_text(errors="replace")
        output_text = (directory / "stdout.log").read_text(errors="replace")
        inner_limit = code != 0 and (
            any(s in error_text for s in ("MemoryError", "bad_alloc", "Cannot allocate memory", "INCONCLUSIVE", "TimeoutExpired"))
            or any(s in output_text for s in ('"termination": "inconclusive"', '"status": "inconclusive"'))
            or code in (-signal.SIGKILL, -signal.SIGXCPU, 137))
        if stop or inner_limit:
            row.update(status="inconclusive", reason=stop or "resource limit reported by child")
        else:
            row["status"] = "success" if code == 0 else "error"
        self.write_receipt()
        if row["status"] != "success":
            self.record["status"] = row["status"]
            raise RuntimeError(f"{name}: {row['status']}; inspect {directory}")
        print(f"{name}: success ({row['elapsed_seconds']} s)", flush=True)
        return directory

    def python(self, *args):
        return [sys.executable, "-B", *map(str, args)]

    def run_a(self, case):
        self.run("a-" + case, self.python("computations/word_a/run_word.py", "--task", case,
                 "--date", "replay", "--seq", "01", "--source-sha256", self.record["source_sha256"]))
        rid = f"word-a-{case}-replay-01"
        rec = read(self.work / "computations/results" / rid / "run.json")
        if rec["post_run"]["termination"] != "success" or rec.get("postcheck", {}).get("passed") is False:
            raise ValueError(f"A {case} did not pass its recorded checks")
        if case in A_APPENDIX:
            result = "script-result-" + RESULT_NAMES.get(case, "result.json")
            compare_json(self.work / "computations/results" / rid / result,
                         self.refs / "appendix-a" / (case + ".json"),
                         self.out / "comparisons" / f"a-{case}-reference.json")

    def run_b_check(self, name, divisor=None):
        key = name + ("_10000" if divisor == 10000 else "")
        destination = self.work / "computations/results" / ("word-b-appendix-" + key + "-replay")
        destination.mkdir(parents=True, exist_ok=False)
        cmd = self.python("computations/word_b/appendix/check_" + name + ".py")
        if divisor is not None:
            cmd.append(str(divisor))
        directory = self.run("appendix-" + key, cmd, {"RUN_OUTDIR": str(destination)})
        result = read(directory / "stdout.log")
        if result.get("all_pass") is not True or result.get("status", "success") != "success":
            raise ValueError(f"Appendix {key} reported failure")
        shutil.copyfile(directory / "stdout.log", destination / "result.json")
        self.b_runs[key] = destination.name
        compare_json(destination / "result.json", self.refs / "appendix-b" / (key + ".json"),
                     self.out / "comparisons" / f"b-{key}-reference.json", B_OPERATIONAL_KEYS)

    def graph_b(self, case, reference=False, small=False):
        args = list(GRAPH_ARGS[case])
        if small:
            args += ["--stop-after", "1"]
        label = ("ref-" if reference else "") + case + ("-small" if small else "")
        raw = f"computations/raw/word-b-{label}-replay"
        (self.work / raw).mkdir(parents=True, exist_ok=False)
        command = self.python("computations/word_b/wgb_ref.py") if reference else ["build/word-replay/wgb"]
        command += args + ["--out", raw]
        self.run("b-" + label, command)
        return raw

    def graph_compare(self, case, left, right, a_layout=False, stages=None, label=None):
        label = label or case
        if case == "q75":
            pairs = [f"q75={left}/{'q75.txt' if a_layout else 'q75_graph.txt'}:{right}/q75_graph.txt"]
        else:
            count = stages if stages is not None else (10 if case == "five-halves" else 4)
            pairs = [f"{case}-{i:02}-{kind}={left}/" +
                     (f"stage-{i:02}-{kind}.txt" if a_layout else f"stage{i}_{kind}.txt") +
                     f":{right}/stage{i}_{kind}.txt" for i in range(count) for kind in ("input", "output")]
        output = f"computations/results/replay-compare-{label}"
        self.run("compare-" + label, self.python("computations/word_b/compare_wordgraph.py", "batch", "--out", output, *pairs))
        report = read(self.work / output / "summary.json")
        if not report["all_identical_and_format_ok"] or len(report["pairs"]) != len(pairs):
            raise ValueError("Incomplete graph comparison")

    def historical_graphs(self, case):
        checks = []
        expected_count = {"five-halves": 20, "cross-75": 8, "q75": 1}[case]
        for implementation in ("A", "B"):
            entries = self.reference["word_graphs"][case][implementation]
            if len(entries) != expected_count or len({e["name"] for e in entries}) != expected_count:
                raise ValueError("Incomplete reference graph set")
            directory = (self.work / f"computations/raw/word-a-{case}-replay-01/dumps" if implementation == "A"
                         else self.work / f"computations/raw/word-b-{case}-replay")
            for entry in entries:
                path = directory / entry["name"]
                if Path(entry["name"]).name != entry["name"]:
                    raise ValueError("Invalid reference graph name")
                matched = path.stat().st_size == entry["bytes"] and digest(path) == entry["sha256"]
                checks.append({"implementation": implementation, "name": entry["name"], "matches_reference_sha256": matched})
        ok = len(checks) == 2 * expected_count and all(row["matches_reference_sha256"] for row in checks)
        save(self.out / "comparisons" / f"graph-{case}-reference.json", {"status": "PASS" if ok else "MISMATCH", "files": checks})
        if not ok:
            raise ValueError(f"Normalized {case} data differ from reference bytes")

    def q75_checks(self):
        for a, b, modulus, cells, carries in ((7, 5, 6, 8, "-4,-2,2,4,6"),
                (7, 5, 15, 8, "-4,-2,2,4,6"), (7, 5, 10, 8, "-4,-2,2,4,6"),
                (5, 2, 6, 4, "-1,1,3"), (3, 2, 6, 4, "-1,1")):
            self.run(f"q75-small-{a}-{b}-{modulus}", self.python("computations/word_b/wgb_ref.py", "q75small",
                     "--a", str(a), "--b", str(b), "--M", str(modulus), "--K", str(cells), "--carries", carries))
        self.run("q75-constants", self.python("computations/word_b/q75_constants.py"))

    def execute(self):
        self.snapshot()
        step_output = self.out / "step"
        self.run("step-" + self.args.scope, self.python(PUBLIC / "reproduce_step.py", "run", "--scope", self.args.scope,
                 "--workspace", self.work, "--output", step_output,
                 "--command-seconds", self.args.command_seconds, "--total-seconds", self.args.total_seconds,
                 "--memory-gib", self.args.memory_gib))
        if read(step_output / "record.json")["status"] != "PASS":
            raise ValueError("One-step reproduction incomplete")
        self.run("compile-b", ["g++", "-O2", "-std=c++17", "computations/word_b/wgb.cpp", "-o", "build/word-replay/wgb"])
        self.q75_checks()
        cases = tuple(GRAPH_ARGS) if self.args.scope == "full" else ("cross-75",)
        for case in cases:
            self.run_a(case)
            b = self.graph_b(case)
            self.graph_compare(case, f"computations/raw/word-a-{case}-replay-01/dumps", b, a_layout=True)
            self.historical_graphs(case)
            ref = self.graph_b(case, reference=True)
            self.graph_compare(case, b, ref, label=case + "-reference")
        if self.args.scope == "preflight":
            b = self.graph_b("five-halves", small=True)
            ref = self.graph_b("five-halves", reference=True, small=True)
            self.graph_compare("five-halves", b, ref, stages=2, label="five-halves-small-reference")
            self.run_a("recurrence")
            for name in ("b01_obr_witness", "b02_interval", "f1_oracle", "r3_example", "w2_return17"):
                self.run_b_check(name)
        else:
            for case in A_APPENDIX:
                self.run_a(case)
            for name in B_FIRST + B_REST:
                self.run_b_check(name)
                if name == "f2_candidates":
                    self.run_b_check(name, divisor=10000)
            config = {"b_runs": self.b_runs, "expected": str(self.refs / "appendix-comparison.json"),
                      "output": str(self.out / "comparisons/appendix-reference.json")}
            save(self.out / "appendix-config.json", config)
            self.run("appendix-comparison", self.python(PUBLIC / "replay.py", "appendix-compare",
                     "--workspace", self.work, "--config", str(self.out / "appendix-config.json")))
        unchanged = []
        for entry in self.inputs:
            src = PUBLIC / entry["path"]
            clone = (self.refs if entry["reference_only"] else self.work) / entry["copy_path"]
            if digest(src) != entry["sha256"] or digest(clone) != entry["sha256"]:
                unchanged.append(entry["path"])
        save(self.out / "input-final-check.json", {"checked": len(self.inputs), "changed": unchanged})
        if unchanged:
            raise ValueError("Input files changed during replay")
        self.record.update(status="PREFLIGHT_PASS" if self.args.scope == "preflight" else "FINITE_COMPUTATIONS_PASS",
                           finished_at=now(), elapsed_seconds=round(time.monotonic() - self.started, 3),
                           scope_description="Finite integer computations and their comparisons")
        self.write_receipt()


def appendix_compare(config):
    """Rebind only locations in the existing comparison module, then call it."""
    cfg = read(config)
    here = ROOT / "computations/word_b/appendix"
    sys.path.insert(0, str(here))
    spec = importlib.util.spec_from_file_location("existing_appendix_comparator", here / "compare_appendix.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.B_RUNS = {k: cfg["b_runs"][v] for k, v in APPENDIX_KEYS.items()}
    module.A_FILES = {key: f"word-a-{case}-replay-01/script-result-{RESULT_NAMES.get(case, 'result.json')}"
                      for key, case in (("finite_height", "finite-height"), ("sieve", "sieve"),
                         ("return_words", "return-words"), ("recurrence", "recurrence"),
                         ("reductions", "reductions"), ("external_budget", "external-budget"))}
    module.A_RAW = str(ROOT / "computations/raw/word-a-finite-height-replay-01/finite_height_witnesses.json")
    module.OUT = str(ROOT / "computations/results/replay-appendix-comparison")
    if Path(module.OUT).exists():
        raise ValueError("Refusing to overwrite appendix comparison")
    module.main()
    result = Path(module.OUT) / "comparison.json"
    if read(result)["all_agree"] is not True:
        raise ValueError("Appendix A/B comparison differs")
    # The existing comparator's summary contains a few informational booleans
    # (some legitimately false). Comparing the entire scientific tree retains
    # these and catches changes not included in its aggregate all_agree flag.
    # The original source receipt records the same two-string set in either
    # Python repr order. Preserve every result field and use the separately
    # tested, exact-field display comparator.
    subprocess.run([sys.executable, "-B", str(PUBLIC / "compare_appendix_display.py"),
                    "--actual", str(result), "--expected", cfg["expected"],
                    "--out", cfg["output"]], check=True, timeout=60)


def main():
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    run = commands.add_parser("run")
    run.add_argument("--scope", choices=("preflight", "full"), required=True)
    run.add_argument("--out", type=Path, required=True)
    run.add_argument("--command-seconds", type=int, default=600)
    run.add_argument("--total-seconds", type=int, default=1800)
    run.add_argument("--memory-gib", type=int, default=8)
    comp = commands.add_parser("appendix-compare")
    comp.add_argument("--config", type=Path, required=True)
    comp.add_argument("--workspace", type=Path, required=True)
    args = parser.parse_args()
    if sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
        parser.error("Python assertions must remain enabled")
    if args.command == "appendix-compare":
        ROOT = args.workspace.resolve()
        appendix_compare(args.config)
        return 0
    if min(args.command_seconds, args.total_seconds, args.memory_gib) <= 0:
        parser.error("Limits must be positive")
    replay = Replay(args)
    try:
        replay.execute()
    except BaseException as error:
        if replay.record["status"] == "running":
            replay.record["status"] = "inconclusive" if isinstance(error, TimeoutError) else "error"
        replay.record.update(error=repr(error), finished_at=now())
        replay.write_receipt()
        raise
    print(replay.record["status"], replay.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
