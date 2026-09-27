# A finite graph certificate for the unshifted 5/3 floor sequence

For every real xi > 0, infinitely many terms floor(xi * (5/3)^n) have a
prime divisor in {2,3,7,11,13,17,19,23,29,31,37}. They are therefore
composite once the terms exceed 37. The product modulus is 1484147626962.

Read **PROOF_JA.md** for the self-contained mathematical argument, exact
finite construction, table, verification scope, provenance, and limitations.

## Contents

* `certificate53.cpp`: exact finite graph producer, checker calls, fixed-cell
  word graphs, phase removal, both-direction exact contraction, prime lifts.
* `audit_basic.hpp`: all-edge rank/phase checker, separate forward-set residue
  check, reconstruction/comparison of all lifted and contracted edges.
* `reference53.py`: different small-instance construction using reachability
  matrices for SCCs and literal forward prime-residue iteration.
* `reproduce.py`: checked replay driver, fixed 5/3 input, failure handling.
* `recorded/`: successful full run and small all-element comparison with its
  ten complete graph dumps. Full large intermediate graphs are regenerated,
  not included in this compact source release.
* `SHA256SUMS`: integrity manifest, not a mathematical certificate.

## Run

Python >= 3.9, g++ with C++17. No nonstandard Python packages are needed.
From this directory, with a previously nonexistent output directory:

```bash
python3 reproduce.py all --out ./replay-all
```

Use `small` or `full` instead of `all` to replay one portion. The default
time limit is 1800 seconds per step; `--timeout` changes it. Full instances
should run one at a time. The recorded full checked run used about 2.54 GiB
peak RSS and 243 seconds on its particular environment; allow memory margin.

The small run deliberately stops at prime 17 with remaining vertices. Its
producer reports `budget_exhausted`, which is NOT a proof by itself. The full
run reaches empty at prime 37, and only that run proves the theorem.

All core arithmetic for finite certification is integer arithmetic. The
adopted proof uses neither interval tightening nor floating-point pruning.
Timers use floating point but do not participate in acceptance.

## Trust boundary

No Lean/kernel proof is included. The checker does not assume that the
producer's SCC partition is correct: sufficient rank and all-letter phase
conditions are verified on every edge. The separate Python generator was
compared element by element only through prime 17, not through prime 37.
All code was developed by the same AI assistant in one research session,
with shared mathematical specifications; no independent human referee or
clean-room authorship is claimed. This is a reproducible computer-assisted
proof with those explicitly stated trust assumptions.
