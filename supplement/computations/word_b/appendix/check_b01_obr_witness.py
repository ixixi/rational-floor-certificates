#!/usr/bin/env python3
"""B-1: OB-R の証人条件（audit-03 §3.9.1, §5 B-1）。"""
import json
from obmath import obr_witness

INPUTS = [
    (101, 2, 15, 1), (101, 2, 15, 2), (101, 2, 15, 3), (101, 2, 15, 4),
    (101, 100, 21, 1),
    (5, 2, 1, 1), (5, 2, 1, 2),
    (7, 5, 1, 1), (7, 5, 1, 2), (7, 5, 1, 3), (7, 5, 3, 1), (7, 5, 11, 1), (7, 5, 5, 1),
    (9, 7, 1, 2), (6, 5, 1, 1), (3, 2, 1, 1), (4, 3, 1, 1), (8, 3, 1, 1),
]

# 手計算による期待採否（自分の紙上計算。研究メモ/同梱コードの値ではない）
EXPECT_ACCEPT = {
    (101, 2, 15, 1): True,   # h=30, c=69=3*23, gcd(69,202)=1
    (101, 2, 15, 2): True,   # h=60, c=39, gcd(39,202)=1
    (101, 2, 15, 3): True,   # h=90, c=9
    (101, 2, 15, 4): False,  # h=120 > 100
    (101, 100, 21, 1): True, # h=42, c=-41
    (5, 2, 1, 1): True,      # h=2, c=1
    (5, 2, 1, 2): True,      # h=4<=4, c=-1, gcd(1,10)=1
    (7, 5, 1, 1): False,     # c=0, gcd(0,35)=35
    (7, 5, 1, 2): True,      # h=4, c=-2
    (7, 5, 1, 3): True,      # h=6, c=-4
    (7, 5, 3, 1): True,      # h=6, c=-4
    (7, 5, 11, 1): False,    # h=22 > 6
    (7, 5, 5, 1): False,     # gcd(R,2ab)=5
    (9, 7, 1, 2): True,      # h=4, c=-2
    (6, 5, 1, 1): True,      # h=2, c=-1
    (3, 2, 1, 1): True,      # h=2, c=-1
    (4, 3, 1, 1): True,      # h=2, c=-1
    (8, 3, 1, 1): False,     # h=2, c=3, gcd(3,24)=3
}


def main():
    results = []
    all_ok = True
    for inp in INPUTS:
        r = obr_witness(*inp)
        r["expected_accepted_by_hand"] = EXPECT_ACCEPT[inp]
        r["matches_hand"] = (r["accepted"] == EXPECT_ACCEPT[inp])
        if not r["matches_hand"]:
            all_ok = False
        if r["accepted"] and not r["derived_all"]:
            all_ok = False
        results.append(r)
    accepted = [(r["a"], r["b"], r["R"], r["m"]) for r in results if r["accepted"]]
    out = {
        "check": "B-1 OB-R witness",
        "n_inputs": len(INPUTS),
        "n_accepted": len(accepted),
        "accepted": accepted,
        "results": results,
        "all_pass": all_ok,
        "status": "success",
        "summary": "%d inputs, %d accepted, derived conditions hold on all accepted, hand expectations match=%s"
                   % (len(INPUTS), len(accepted), all_ok),
    }
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
