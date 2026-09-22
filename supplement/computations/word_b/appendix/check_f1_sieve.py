#!/usr/bin/env python3
"""B-F1/B-C1 用の全語列挙: fh_sieve.cpp をビルドし (6,5,40) と (9,7,18) を実行、出力を固定する。"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
BUILD = os.path.join(ROOT, "build", "word-appendix")
FH = os.path.join(BUILD, "fh")
CASES = [(6, 5, 40), (9, 7, 18)]


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def build():
    os.makedirs(FH, exist_ok=True)
    src = os.path.join(HERE, "fh_sieve.cpp")
    binp = os.path.join(BUILD, "fh_sieve")
    subprocess.check_call(["g++", "-O2", "-std=c++17", "-o", binp, src])
    return binp, sha(src), sha(binp)


def main():
    binp, src_sha, bin_sha = build()
    outdir = os.environ.get("RUN_OUTDIR", FH)
    results = []
    all_ok = True
    for (a, b, N) in CASES:
        prefix = os.path.join(FH, "%d_%d_%d" % (a, b, N))
        t0 = time.monotonic()
        subprocess.check_call([binp, str(a), str(b), str(N), prefix])
        el = time.monotonic() - t0
        counts = json.load(open(prefix + ".counts.json"))
        cand_path = prefix + ".candidates.txt"
        n_cand_lines = sum(1 for _ in open(cand_path))
        rec = {"a": a, "b": b, "N": N, "elapsed_seconds": round(el, 3), "counts": counts,
               "candidates_file": os.path.relpath(cand_path, ROOT), "candidates_sha256": sha(cand_path),
               "counts_sha256": sha(prefix + ".counts.json"), "n_candidate_lines": n_cand_lines}
        ch = {}
        ch["A_0 = 1"] = counts["A"][0] == 1
        ch["leaves = A_N"] = counts["leaves"]["total"] == counts["A"][N]
        ch["classification sums to leaves"] = sum(counts["leaves"][k] for k in ("small", "even", "roots", "candidates")) == counts["leaves"]["total"]
        ch["candidate lines = candidates"] = n_cand_lines == counts["leaves"]["candidates"]
        ch["seed consistency a^j s + C_j = 0 mod b^j all leaves"] = counts["seed_consistency_failures"] == 0
        ch["node count identity: A_j*|alph| = A_{j+1} + rejI_{j+1} + rejR_{j+1}"] = all(
            counts["A"][j] * len(counts["alphabet"]) == counts["A"][j + 1] + counts["rejected_interval_by_depth"][j + 1] + counts["rejected_roots_by_depth"][j + 1] for j in range(N))
        rec["checks"] = ch
        rec["all_pass"] = all(ch.values())
        all_ok &= rec["all_pass"]
        results.append(rec)
        for ext in (".counts.json", ".candidates.txt"):
            shutil.copy(prefix + ext, os.path.join(outdir, os.path.basename(prefix) + ext))
    out = {"check": "B-F1/B-C1 full enumeration (fh_sieve)", "source_sha256": src_sha, "binary_sha256": bin_sha,
           "compiler": subprocess.check_output(["g++", "--version"]).decode().splitlines()[0],
           "results": results, "all_pass": all_ok, "status": "success",
           "summary": "; ".join("(%d,%d,N=%d): A_N=%d small=%d even=%d roots=%d cand=%d in %.1fs" % (
               r["a"], r["b"], r["N"], r["counts"]["A"][r["N"]], r["counts"]["leaves"]["small"], r["counts"]["leaves"]["even"],
               r["counts"]["leaves"]["roots"], r["counts"]["leaves"]["candidates"], r["elapsed_seconds"]) for r in results)}
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
