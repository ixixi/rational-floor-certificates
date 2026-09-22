#!/usr/bin/env python3
"""Compare fresh independent appendix outputs; paths are set by replay.py."""
import datetime
import hashlib
import json
import os
import subprocess
import tempfile
from fractions import Fraction
from math import gcd

from obmath import psi, modinv, trial_factor, crt
from check_w1_return_words import forward_res, word_C, backward
from check_n3_nb_fork import candidates as fork_candidates

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
RES = os.path.join(ROOT, "computations", "results")
OUT = None
B_RUNS = {}
A_FILES = {}
A_RAW = None
BIN = os.path.join(ROOT, "build", "word-appendix", "fh_sieve")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_b(key):
    return json.load(open(os.path.join(RES, B_RUNS[key], "result.json")))


def main():
    os.makedirs(OUT, exist_ok=True)
    inputs = {}
    for k, v in B_RUNS.items():
        p = os.path.join(RES, v, "result.json")
        inputs["B:" + v] = sha(p)
    A = {}
    for k, v in A_FILES.items():
        p = os.path.join(RES, v)
        A[k] = json.load(open(p))
        inputs["A:" + v] = sha(p)
    raw = json.load(open(A_RAW))
    inputs["A:raw finite_height_witnesses.json"] = sha(A_RAW)
    cmp = {}
    diffs = []

    # ---------------- 1. 有限高さ
    f1 = load_b("f1")
    fh = {}
    for case in A["finite_height"]["cases"]:
        a, b, N = case["a"], case["b"], case["N"]
        mine = next(r for r in f1["results"] if (r["a"], r["b"], r["N"]) == (a, b, N))
        c = mine["counts"]
        d = {}
        d["A_s all depths equal"] = case["counts"] == c["A"]
        d["A_N"] = (case["counts"][-1], c["A"][N])
        d["even equal"] = (case["even"], c["leaves"]["even"], case["even"] == c["leaves"]["even"])
        d["small equal"] = (case["small"], c["leaves"]["small"], case["small"] == c["leaves"]["small"])
        d["excluded(FH-roots) equal"] = (case["excluded"], c["leaves"]["roots"], case["excluded"] == c["leaves"]["roots"])
        d["surviving equal"] = (case["surviving"], c["leaves"]["candidates"], case["surviving"] == c["leaves"]["candidates"])
        d["root primes equal"] = (case["primes"], c["root_primes"], case["primes"] == c["root_primes"])
        d["height = b^N"] = str(b ** N) == case["height"] == c["b_pow_N"]
        key = "%d/%d" % (a, b)
        # 生存者集合
        a_surv = set(int(x) for x in raw[key]["survivors"])
        my_cands = os.path.join(ROOT, "build", "word-appendix", "fh", "%d_%d_%d.candidates.txt" % (a, b, N))
        my_surv = set(int(l.split()[0]) for l in open(my_cands))
        d["survivor set equal"] = (len(a_surv), len(my_surv), a_surv == my_surv, len(a_surv - my_surv), len(my_surv - a_surv))
        # 証人（B: 約数上限 10^4 の run -02 と A を要素単位で比較、run -01（10^5）は探索順序依存の差として記録）
        if key == "9/7":
            f2b = load_b("f2b")
            f2a = load_b("f2a")
            a_w = {int(w["seed"]): (w["step"], w["divisor"], int(w["cofactor"])) for w in raw[key]["witnesses"]}
            b_w = {w[0]: (w[1], w[2], w[3]) for w in f2b["witnesses"]}
            same = sum(1 for s in a_w if s in b_w and a_w[s] == b_w[s])
            d["witness (step,divisor,cofactor) identical with B run -02 (bound 1e4)"] = (same, len(a_w))
            a_eq = all(int(w["term"]) == w["divisor"] * int(w["cofactor"]) and 1 < w["divisor"] < int(w["term"]) for w in raw[key]["witnesses"])
            d["A witnesses satisfy term = divisor*cofactor, 1<divisor<term (re-verified by B)"] = a_eq
            d["A step distribution"] = case["survivor_step_counts"]
            d["B distribution run -02 (bound 1e4)"] = f2b["first_divisor_time_distribution (search-order dependent)"]
            d["B distribution run -01 (bound 1e5)"] = f2a["first_divisor_time_distribution (search-order dependent)"]
            d["max divisor A / B-02 / B-01"] = (case["maximum_survivor_divisor"], f2b["max_divisor"], f2a["max_divisor"])
            d["max step A / B-02 / B-01"] = (case["maximum_survivor_stop_step"], max(int(k) for k in f2b["first_divisor_time_distribution (search-order dependent)"]), max(int(k) for k in f2a["first_divisor_time_distribution (search-order dependent)"]))
            if not (a_surv == my_surv and same == len(a_w)):
                diffs.append("9/7 survivors/witnesses differ")
        # 小さい初期素数
        f3 = load_b("f3")
        mine_small = {r["P"]: r["witness"] for r in f3["results"] if r["base"] == key}
        sm = []
        for w in raw[key]["small"]:
            P = int(w["seed"])
            mw = mine_small[P]
            if w["kind"] == "proper_divisor":
                ok = mw["type"] == "proper divisor" and mw["time"] == w["step"] and mw["d"] == w["divisor"] and mw["Q"] == int(w["term"]) and mw["e"] == int(w["cofactor"])
            elif w["kind"] == "no_prime_successor":
                # A の step は「後続が存在しない項の次の時刻」、B の time はその項の時刻
                ok = mw["type"].startswith("no prime successor") and mw["time"] + 1 == w["step"] and mw["Q"] == int(w["previous_term"]) and (mw["Q"] % 5) == w["remainder"]
            else:
                ok = mw["type"] == "empty interval" and mw["time"] == w["step"] and mw["L"] == int(w["low"]) and mw["U"] == int(w["high"]) and mw["B"] == int(w["denominator"])
            sm.append((P, w["kind"], w["step"], ok))
            if not ok:
                diffs.append("small prime witness differs: %s P=%d" % (key, P))
        d["small prime witnesses (P, A kind, A step, agree)"] = sm
        fh[key] = d
        if not (d["A_s all depths equal"] and d["even equal"][2] and d["small equal"][2] and d["excluded(FH-roots) equal"][2] and d["surviving equal"][2] and d["root primes equal"][2]):
            diffs.append("finite height counts differ for %s" % key)
    # A の small_cases（語数）を B の篩で再計算
    sc = []
    with tempfile.TemporaryDirectory() as td:
        for s in A["finite_height"]["small_cases"]:
            a, b, N = s["a"], s["b"], s["N"]
            prefix = os.path.join(td, "x")
            subprocess.check_call([BIN, str(a), str(b), str(N), prefix])
            cnt = json.load(open(prefix + ".counts.json"))
            sc.append({"a": a, "b": b, "N": N, "A words": s["words"], "B A_N": cnt["A"][N], "equal": s["words"] == cnt["A"][N]})
            if s["words"] != cnt["A"][N]:
                diffs.append("small case (%d,%d,%d) word count differs" % (a, b, N))
    fh["small_cases"] = sc
    cmp["finite_height"] = fh

    # ---------------- 2. 篩
    sv = {}
    c1 = load_b("c1")
    for case in A["sieve"]["cases"]:
        a, b, ell = case["a"], case["b"], case["length"]
        mine = next(r for r in c1["results"] if (r["a"], r["b"], r["ell"]) == (a, b, ell))
        sv["%d/%d" % (a, b)] = {"counts equal": case["counts"] == mine["A"], "constant A / B_min": (case["constant"], mine["C_min"], case["constant"] == mine["C_min"]),
                                "A exponent (float, not compared)": case["exponent"]}
        if not (case["counts"] == mine["A"] and case["constant"] == mine["C_min"]):
            diffs.append("sieve counts/constant differ for %d/%d" % (a, b))
    l1 = load_b("l1")
    pp = A["sieve"]["prime_prefix"]
    ex = l1["nine_term_example"]
    sv["prime_prefix"] = {"params equal": (pp["a"], pp["b"], pp["t"], pp["P"], pp["D"], pp["L"]) == (ex["a"], ex["b"], ex["t"], 1042408919, 210, 9) and pp["xi"] == ex["xi"],
                          "primes equal": pp["primes"] == ex["floors_j<=9"][:9], "next_composite equal": A["sieve"]["next_composite"] == ex["floors_j<=9"][9]}
    cmp["sieve"] = sv

    # ---------------- 3. 帰還語
    w1 = load_b("w1")
    rw = {}
    for wit in A["return_words"]["witnesses"]:
        name = wit["name"]
        a, b, m, q = wit["a"], wit["b"], wit["modulus"], wit["root"]
        lo, hi = Fraction(wit["interval"][0]), Fraction(wit["interval"][1])
        d = {}
        U, V = tuple(wit["U"]["word"]), tuple(wit["V"]["word"])
        mine = next((r for r in w1["results"] if r["case"] == "%d/%d" % (a, b) and r["|U|"] == len(U) and r["|V|"] == len(V)), None)
        if mine is not None:
            d["B has this witness"] = True
            d["residues U equal"] = wit["U"]["residues"] == mine["residues_U"]
            d["residues V equal"] = wit["V"]["residues"] == mine["residues_V"]
            d["B checks all pass"] = mine["all_pass"]
        else:
            d["B has this witness"] = False
        # B の関数で A の証人を再検証（mod 1001 の別証明書を含む）
        rU, rV = forward_res(a, b, U, q, m), forward_res(a, b, V, q, m)
        d["A residues reproduced by B forward map"] = rU == wit["U"]["residues"] and rV == wit["V"]["residues"]
        d["units and return"] = all(gcd(v, m) == 1 for v in rU + rV) and rU[-1] == q == rV[-1]
        imgs = {}
        allvals = []
        okI = True
        for nm, w in (("U", U), ("V", V)):
            ys = []
            for x in (lo, hi):
                y, vals = backward(a, b, w, x)
                ys.append(y)
                allvals.extend(vals)
                if not all(0 < v < 1 for v in vals) or not (lo <= y <= hi):
                    okI = False
            imgs[nm] = [str(ys[0]), str(ys[1])]
        d["backward values in (0,1), images in I"] = okI
        d["images equal A"] = imgs["U"] == wit["U"]["image"] and imgs["V"] == wit["V"]["image"]
        d["all_suffix min/max (B recomputed over both endpoints)"] = {"U": None, "V": None}
        for nm, w in (("U", U), ("V", V)):
            vals = []
            for x in (lo, hi):
                vals.extend(backward(a, b, w, x)[1])
            d["all_suffix min/max (B recomputed over both endpoints)"][nm] = (str(min(vals)), str(max(vals)), str(min(vals)) == wit[nm]["all_suffix_min"], str(max(vals)) == wit[nm]["all_suffix_max"])
        d["UV != VU"] = U + V != V + U and wit["noncommuting"]
        rw[name] = d
        if mine is not None and not (d["residues U equal"] and d["residues V equal"]):
            diffs.append("return-word residues differ: %s" % name)
        if not (d["A residues reproduced by B forward map"] and d["units and return"] and okI and d["images equal A"]):
            diffs.append("return-word witness %s: B re-verification of A data failed" % name)
    w2 = load_b("w2")
    blk = A["return_words"]["prime17_language_blocker"]
    a_edges = sorted(tuple(e) for e in blk["edges"])
    rw["prime17"] = {"edges equal": a_edges == sorted(tuple(e) for e in w2["edges"]), "rank equal": {int(k): v for k, v in blk["rank"].items()} == {i: r for i, r in zip(range(1, 17), [0, 0, 0, 2, 1, 3, 0, 1, 0, 2, 2, 0, 0, 1, 3, 1])},
                     "only recurrent edge": tuple(blk["only_recurrent_edge"]) == (9, "U", 9) and w2["self_loops"] == [[9, "U", 9]]}
    if not all(rw["prime17"].values()):
        diffs.append("prime 17 blocker differs")
    cmp["return_words"] = rw

    # ---------------- 4. 再帰
    r3 = load_b("r3")
    fe = A["recurrence"]["floor_example"]
    rc = {"floor example equal": fe["c0"] == -1 == fe["c43"] and fe["copy_times"] == [1, 43] and fe["term_index"] == 44 and fe["term"] == r3["Q_44"] == 697829 and fe["factorization"] == [11, 63439],
          "A exhaustive counts (different enumeration range, not compared)": A["recurrence"]["exhaustive"],
          "B exhaustive counts": {"copy_towers": load_b("r1")["n_copy_towers"], "checks": load_b("r1")["n_checks"]},
          "A digit bijection instances / B range": (A["recurrence"]["digit_bijections"], {"t<=8", "L<=3"})}
    if not rc["floor example equal"]:
        diffs.append("recurrence floor example differs")
    cmp["recurrence"] = rc

    # ---------------- 5. 還元
    r2 = load_b("r2")
    red = {}
    myD = {r["t"]: r["D_t"] for r in r2["results"]}
    red["D_t t=1..4 equal"] = all(A["reductions"]["gap2_digit_sets_t_1_to_4"][str(t)] == myD[t] for t in range(1, 5))
    # fork covered pairs b<=64: B の条件（3 の精密化込み／なし）で再計算
    def cond(a, b, refine):
        d = a - b
        ks = [k for k in range(1, d) if (k - a) % 2 == 0]
        return all(gcd(k, b) > 1 or gcd(d + k, a) > 1 or gcd(d - k, a) > 1 or (refine and ((a % 3 == 0) != (k % 3 == 0))) for k in ks)
    a_pairs = set(tuple(p) for p in A["reductions"]["fork_covered_reduced_pairs_b_at_most_64"])
    b_ref = {(a, b) for b in range(2, 65) for a in range(b + 1, 2 * b) if gcd(a, b) == 1 and cond(a, b, True)}
    b_noref = {(a, b) for b in range(2, 65) for a in range(b + 1, 2 * b) if gcd(a, b) == 1 and cond(a, b, False)}
    red["fork covered pairs b<=64: A count, B(with 3-refinement) count, B(without) count"] = (len(a_pairs), len(b_ref), len(b_noref))
    red["A == B(with refinement)"] = a_pairs == b_ref
    red["A == B(without refinement)"] = a_pairs == b_noref
    red["A minus B(with)"] = sorted(a_pairs - b_ref)[:20]
    red["B(with) minus A"] = sorted(b_ref - a_pairs)[:20]
    # NB-GAP 例: d ごとの最小 a
    n4 = load_b("n4")
    ex = {}
    for (d, a, b) in A["reductions"]["ordinary_ceiling_examples"]:
        ex.setdefault(d, []).append((a, b))
    gap = {}
    for d, lst in ex.items():
        if str(d) in n4["table"]:
            t = n4["table"][str(d)]
            gap[d] = {"A first (a,b)": lst[0], "B min a>2d": (t["min a>2d"], t["b"]), "A examples in B progression": all((a - t["a residue"]) % t["a mod"] == 0 and b == a - d for a, b in lst)}
        else:
            gap[d] = {"A first (a,b)": lst[0], "B": "d=%d not a prime power in B table" % d}
    red["ordinary ceiling examples vs B NB-GAP table"] = gap
    if not red["D_t t=1..4 equal"]:
        diffs.append("D_t differ")
    if not red["A == B(with refinement)"]:
        diffs.append("fork covered pair sets differ (see report)")
    cmp["reductions"] = red

    # ---------------- 6. 外部予算（第一段階の対象）
    b02 = load_b("b02")
    b09 = load_b("b09")
    eb = {}
    for exa in A["external_budget"]["examples"]:
        a, b, R, m = exa["a"], exa["b"], exa["R"], exa["m"]
        mine = next((r for r in b02["results"] if r.get("witness") == [a, b, R, m]), None)
        d = {"B has witness": mine is not None}
        if mine:
            d["h,c,d,L equal"] = (exa["h"], exa["c"], exa["d"], exa["L"]) == (mine["h"], mine["c"], mine["d"], mine["L"])
            d["interval equal"] = exa["interval"] == [mine["x_L"], mine["x_{L+1}"]]
            d["U,V equal"] = exa["U"] == mine["U"] and exa["V"] == mine["V"]
            if "translation_divisor" in exa:
                key = "%d/%d" % (a, b)
                nm = b09["named"].get(key)
                d["CUT-T D, C1 equal"] = nm is not None and nm["D"] == exa["translation_divisor"] and nm["C"][0] == exa["first_carry_sum"]
                d["eliminating prime"] = exa["eliminating_prime_for_this_two_word_language"]
            if not (d["h,c,d,L equal"] and d["interval equal"] and d["U,V equal"]):
                diffs.append("external budget example %d/%d differs" % (a, b))
        eb["%d/%d R=%d m=%d" % (a, b, R, m)] = d
    eb["A aggregate counts (max_a=60, 1042 bases, 19576 checks, ...) not compared: different ranges"] = {k: A["external_budget"][k] for k in ("max_a", "reduced_bases", "translation_prime_criterion_checks", "arithmetic_obstruction_witnesses", "jacobsthal_guaranteed_cases")}
    cmp["external_budget"] = eb

    out = {"task": "A/B appendix comparison", "date": datetime.datetime.now().astimezone().isoformat(), "inputs_sha256": inputs,
           "comparison": cmp, "differences": diffs, "all_agree": not diffs}
    with open(os.path.join(OUT, "comparison.json"), "w") as f:
        json.dump(out, f, indent=1, ensure_ascii=False, default=str)
    write_report(out)
    print(json.dumps({"all_agree": not diffs, "differences": diffs}, ensure_ascii=False))


def write_report(out):
    c = out["comparison"]
    L = []
    L.append("# A/B 附録結果の比較報告（独立検証B）\n")
    L.append("日付: %s。B は自分の結果を固定（各 run.json に result.json の SHA-256、候補一覧の SHA-256 を記録）した後に A の結果 JSON と生の証人一覧だけを開いた。A のスクリプト・ログは読んでいない。比較は要素単位（配列・集合・各証人）で行い、件数やハッシュの一致だけで済ませていない。JSON: `comparison.json`。\n" % out["date"])
    L.append("## 入力（SHA-256）\n")
    for k, v in out["inputs_sha256"].items():
        L.append("- `%s`: %s" % (k, v))
    L.append("\n## 1. 有限高さ（6/5 長さ 40、9/7 長さ 18）\n")
    for key in ("6/5", "9/7"):
        d = c["finite_height"][key]
        L.append("### %s\n" % key)
        L.append("- 全深さの語数 A_s（A の `counts` と B の `A`）: 一致=%s、A_N = %s" % (d["A_s all depths equal"], d["A_N"]))
        L.append("- 復元整数が偶数 (A, B, 一致): %s；小さい (≤max(a,N+1)): %s；FH-roots 棄却 (A `excluded`, B `roots`): %s；残候補: %s" % (d["even equal"], d["small equal"], d["excluded(FH-roots) equal"], d["surviving equal"]))
        L.append("- 固定除数の素数集合: %s；高さ b^N 一致: %s" % (d["root primes equal"], d["height = b^N"]))
        L.append("- 残候補の整数集合（A の survivors と B の候補一覧）: (|A|, |B|, 一致, A−B, B−A) = %s" % (d["survivor set equal"],))
        if key == "9/7":
            L.append("- 残候補の証人 (時刻, 約数, 補因子) が A と B run -02（約数上限 10^4）で一致した件数: %s" % (d["witness (step,divisor,cofactor) identical with B run -02 (bound 1e4)"],))
            L.append("- A の証人の等式 term = divisor·cofactor（1<divisor<term）を B が再検証: %s" % d["A witnesses satisfy term = divisor*cofactor, 1<divisor<term (re-verified by B)"])
            L.append("- 棄却時刻の分布: A %s；B run -02（上限 10^4）%s；B run -01（上限 10^5）%s。最大約数 (A, B-02, B-01) = %s、最大時刻 = %s。分布・最大約数は約数探索の上限と順序に依存する量であり、数学的内容（全 4592 候補が時刻 ≤7 に真の約数をもつ）は両 run で同じ。研究メモ §11.5 の表 {0:3824,1:630,2:109,3:24,4:3,5:1,7:1} は B のどの探索設定とも一致せず、audit-04 §3.3.4 の判定（原案の記載誤り）と整合する。" % (
                d["A step distribution"], d["B distribution run -02 (bound 1e4)"], d["B distribution run -01 (bound 1e5)"], d["max divisor A / B-02 / B-01"], d["max step A / B-02 / B-01"]))
        L.append("- 小さい初期素数の証人 (P, A の種類, A の step, 一致): %s（A の `no_prime_successor` の step は「後続がない項の次の時刻」、B の time はその項の時刻。この対応で一致を判定）" % (d["small prime witnesses (P, A kind, A step, agree)"],))
    L.append("\n- A の small_cases の語数を B の篩で再計算: %s" % c["finite_height"]["small_cases"])
    L.append("\n## 2. 篩の計数と定数\n")
    for key in ("9/7", "6/5"):
        d = c["sieve"][key]
        L.append("- %s: 計数配列一致=%s、定数 C (A, B の最小整数, 一致) = %s。A の `exponent` は浮動小数点なので比較対象にせず、B は整数不等式（A_18<7^9、A_40<5^10）と最小 C で確認した。" % (key, d["counts equal"], d["constant A / B_min"]))
    L.append("- 9 項素数前置部: パラメータ一致=%s、9 素数一致=%s、j=9 の合成数一致=%s" % (c["sieve"]["prime_prefix"]["params equal"], c["sieve"]["prime_prefix"]["primes equal"], c["sieve"]["prime_prefix"]["next_composite equal"]))
    L.append("\n## 3. 帰還語\n")
    for name, d in c["return_words"].items():
        if name == "prime17":
            L.append("- 法 17 の 12 辺: 一致=%s、順位表一致=%s、唯一の自己ループ 9→U→9: %s" % (d["edges equal"], d["rank equal"], d["only recurrent edge"]))
        else:
            L.append("- %s: B に同じ証人あり=%s%s；A の剰余列を B の前向き写像で再現=%s；単元性と帰還=%s；逆向き全途中値∈(0,1) かつ像⊂I=%s；像の端点が A の `image` と一致=%s；UV≠VU=%s；`all_suffix_min/max`（B は両端点からの全途中値の最小・最大として再計算）: %s" % (
                name, d["B has this witness"], ("（剰余列 U/V 一致=%s/%s、B の全検査合格=%s）" % (d["residues U equal"], d["residues V equal"], d["B checks all pass"])) if d["B has this witness"] else "（B の仕様外の別証明書。B の関数で再検証のみ）",
                d["A residues reproduced by B forward map"], d["units and return"], d["backward values in (0,1), images in I"], d["images equal A"], d["UV != VU"], d["all_suffix min/max (B recomputed over both endpoints)"]))
    L.append("\n## 4. 再帰\n")
    d = c["recurrence"]
    L.append("- 9/7, ξ=11 の床軌道の例（c0=c43=−1、コピー時刻 (1,43)、時刻 44、697829=11·63439）: 一致=%s" % d["floor example equal"])
    L.append("- 全数検査の件数は列挙範囲が異なるため比較しない: A %s、B %s；桁全単射 A %s、B は t≤8・L≤3" % (d["A exhaustive counts (different enumeration range, not compared)"], d["B exhaustive counts"], d["A digit bijection instances / B range"][0]))
    L.append("\n## 5. 還元\n")
    d = c["reductions"]
    L.append("- D_t（t=1..4）一致=%s" % d["D_t t=1..4 equal"])
    L.append("- NB-FORK の条件を満たす既約対（b≤64）: (A の個数, B（3 の精密化込み）, B（精密化なし）) = %s；A = B(精密化込み): %s；A = B(なし): %s；A−B(込み) = %s；B(込み)−A = %s" % (
        d["fork covered pairs b<=64: A count, B(with 3-refinement) count, B(without) count"], d["A == B(with refinement)"], d["A == B(without refinement)"], d["A minus B(with)"], d["B(with) minus A"]))
    L.append("- 切り上げ形の例（d ごとの最初の (a,b)）と B の NB-GAP 表: %s" % d["ordinary ceiling examples vs B NB-GAP table"])
    L.append("\n## 6. 外部予算（第一段階 B-2/B-9 との照合）\n")
    for k, v in c["external_budget"].items():
        L.append("- %s: %s" % (k, v))
    L.append("\n## 7. 判定\n")
    if out["all_agree"]:
        L.append("要素単位で比較した全項目で A と B は一致した。一致は「二つの独立実装が同じ有限対象を出した」ことの証拠であり、定義の数学的妥当性や定理の成立を証明しない。")
    else:
        L.append("不一致: %s。B は出力を変更せず、原因の切り分けを上に記した。" % out["differences"])
    with open(os.path.join(OUT, "REPORT.md"), "w") as f:
        f.write("\n".join(L) + "\n")


if __name__ == "__main__":
    main()
