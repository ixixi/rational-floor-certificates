#!/usr/bin/env python3
"""compare_five_thirds.py -- stage-by-stage comparison of B's two-direction 5/3 run with the handoff producer.

Usage:
  compare_five_thirds.py --canon BIN --b-dir DIR --b-json FILE --a-prefix PREFIX --a-json FILE
                         --stages N --out OUT.json [--elementwise TMPDIR]

Inputs:
  * B: `wgb pipeline ... --bidir` graph dumps DIR/stage<k>_input.txt, DIR/stage<k>_output.txt
    (WORDGRAPH 2) and its JSON lines FILE.
  * A: the handoff producer's dumps PREFIX_<k>_in.txt, PREFIX_<k>_out.txt, written when a prefix is
    given as its sixth argument, and its result JSON.  Only the dump format and the documented JSON
    fields are used; the producer's source is not needed.

For each stage both graphs are brought to the canonical text of canon_wordgraph (B's vertices are
ordered by (cell, residue modulo each prime in the order used)); the SHA-256 of the canonical texts
and the counts must agree.  The per-stage cyclic and certified component counts and the output
vertex, edge, letter and maximum-word-length counts in the two JSON records must agree as well.
With --elementwise the two canonical texts are also compared byte for byte (element by element).
"""
import argparse, filecmp, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor


def canon(binary, path, text_out=None):
    r = subprocess.run([binary, path] + (["--canonical-out", text_out] if text_out else []),
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"canon_wordgraph failed on {path}: {r.stderr.strip()}")
    d = json.loads(r.stdout)
    if d.get("status") != "ok" or d.get("duplicate_rows"):
        raise SystemExit(f"unexpected canonical summary for {path}: {d}")
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--canon", required=True)
    ap.add_argument("--b-dir", required=True)
    ap.add_argument("--b-json", required=True)
    ap.add_argument("--a-prefix", required=True)
    ap.add_argument("--a-json", required=True)
    ap.add_argument("--stages", type=int, required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--jobs", type=int, default=2, help="canonicalisations run in parallel (default 2)")
    ap.add_argument("--elementwise", metavar="DIR",
                    help="also write both canonical texts to DIR, compare them byte for byte, then delete them")
    args = ap.parse_args()

    b_stage = {}
    for line in open(args.b_json):
        d = json.loads(line)
        if d.get("event") in ("stage", "bidir"):
            b_stage.setdefault(d["stage"], {}).update({d["event"]: d})
    a = json.load(open(args.a_json))
    a_stages = a["stages"]

    rows, ok = [], True
    for k in range(args.stages):
        row = {"stage": k}
        bs, bb = b_stage[k]["stage"], b_stage[k]["bidir"]
        ast = a_stages[k]
        row["prime"] = bs["prime"]
        counts = {
            "prime": (bs["prime"], ast["p"]),
            "in_vertices": (bs["in_vertices"], ast["vin"]),
            "in_edges": (bs["in_edges"], ast["ein"]),
            "cyclic": (bs["cyclic"], ast["cyclic"]),
            "certified": (bs["certified"], ast["certified"]),
            "retained_vertices": (bs["uncertified_vertices"], ast["retained"]),
            "out_vertices": (bb["out_vertices"], ast["vout"]),
            "out_edges": (bb["out_edges"], ast["eout"]),
            "out_letters": (bb["out_total_chars"], ast["letters"]),
            "out_max_word_length": (bb["out_max_word_length"], ast["maxlen"]),
        }
        row["counts"] = {key: {"B": x, "A": y, "equal": x == y} for key, (x, y) in counts.items()}
        ok &= all(v["equal"] for v in row["counts"].values())
        for side, bpath, apath in (("in", f"{args.b_dir}/stage{k}_input.txt", f"{args.a_prefix}_{k}_in.txt"),
                                   ("out", f"{args.b_dir}/stage{k}_output.txt", f"{args.a_prefix}_{k}_out.txt")):
            tb = ta = None
            if args.elementwise:
                os.makedirs(args.elementwise, exist_ok=True)
                tb = os.path.join(args.elementwise, f"B_{k}_{side}.canon")
                ta = os.path.join(args.elementwise, f"A_{k}_{side}.canon")
            with ThreadPoolExecutor(max_workers=max(1, min(2, args.jobs))) as pool:
                fb = pool.submit(canon, args.canon, bpath, tb)
                fa = pool.submit(canon, args.canon, apath, ta)
                cb, ca = fb.result(), fa.result()
            same = all(cb[f] == ca[f] for f in ("vertices", "edges", "letters", "max_word_length", "D", "sha256"))
            row[side] = {"B": cb, "A": ca, "equal": same}
            if args.elementwise:
                identical = filecmp.cmp(tb, ta, shallow=False)
                row[side]["canonical_texts_identical_bytes"] = identical
                same = same and identical
                row[side]["equal"] = same
                os.remove(tb)
                os.remove(ta)
            ok &= same
        rows.append(row)
        print(json.dumps({"stage": k, "prime": row["prime"], "counts_equal": all(v["equal"] for v in row["counts"].values()),
                          "in_equal": row["in"]["equal"], "out_equal": row["out"]["equal"],
                          "in_sha256": row["in"]["B"]["sha256"], "out_sha256": row["out"]["B"]["sha256"]}), flush=True)

    result = {"status": "all_stages_match" if ok else "mismatch", "stages": rows,
              "normalisation": "canon_wordgraph CANON1: B vertices ordered by (cell, residues modulo the used primes in order); "
                               "A vertex indices as dumped; edges sorted by (u, v, word); SHA-256 of the canonical text"}
    with open(args.out, "w") as f:
        json.dump(result, f, indent=1)
        f.write("\n")
    print(json.dumps({"status": result["status"], "stages": len(rows)}))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
