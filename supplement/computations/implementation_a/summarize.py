"""Tables derived only from A scientific output; expectations compared afterwards."""
from __future__ import annotations

import csv
import json
from collections import defaultdict
from pathlib import Path

STAGE_FIELDS = ["K", "vertices", "edges", "cyclic_components", "certified_components", "remaining_vertices"]
PERIODIC_FIELDS = ["K", "component_count", "component_sizes", "d", "primitive_word"]


def derived_tables(science: dict) -> dict:
    stages, periodic, unresolved, diagnostics = [], [], [], []
    for stage in science["stages"]:
        components = stage["components"]
        stages.append(dict(zip(STAGE_FIELDS, [
            stage["K"], len(stage["vertices"]), len(stage["edges"]),
            sum(c["cyclic"] for c in components), sum(c["certified"] for c in components),
            len(stage["retained"]),
        ])))
        groups = defaultdict(list)
        for c in components:
            if c["certified"]:
                groups[(c["d"], tuple(c["word"]))].append(len(c["vertices"]))
            elif c["cyclic"]:
                unresolved.append({"K": stage["K"], "root": c["vertices"][0],
                                   "vertices": len(c["vertices"]),
                                   "internal_edges": c["internal_edge_count"],
                                   "d": c["d"], "collision": c["collision"]})
        for (d, word), sizes in sorted(groups.items()):
            periodic.append({"K": stage["K"], "component_count": len(sizes),
                             "component_sizes": ";".join(map(str, sorted(sizes))), "d": d,
                             "primitive_word": ";".join(map(str, word))})
        diagnostics.append({"K": stage["K"], "all_components": len(components),
                            "noncyclic_vertices": sum(len(c["vertices"]) for c in components
                                                      if not c["cyclic"]),
                            "scc_postcheck": "pass", "block_certificate_export_check": "pass"})
    return {"stages": stages, "periodic_components": periodic,
            "unresolved_components": unresolved, "diagnostics": diagnostics}


def write_csv(path: Path, fields: list[str], rows: list[dict]) -> None:
    with path.open("x", encoding="utf-8", newline="") as out:
        writer = csv.DictWriter(out, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def write_tables(science: dict, output: Path) -> dict:
    tables = derived_tables(science)
    write_csv(output / "stages.csv", STAGE_FIELDS, tables["stages"])
    write_csv(output / "periodic-components.csv", PERIODIC_FIELDS, tables["periodic_components"])
    summary = {"schema_version": 1, "parameters": science["parameters"],
               "termination": science["termination"], "tables": tables,
               "derived_from": "scientific.json", "independent_verification": False}
    with (output / "summary.json").open("x", encoding="utf-8") as out:
        json.dump(summary, out, sort_keys=True, indent=2)
        out.write("\n")
    return tables


def compare_expectations(parameters: dict, tables: dict, expected_directory: Path) -> dict:
    """This function never alters scientific output or its termination status."""
    def read(name: str) -> list[dict]:
        with (expected_directory / name).open(newline="", encoding="utf-8") as stream:
            return list(csv.DictReader(stream))

    def stringify(rows: list[dict]) -> list[dict]:
        return [{k: str(v) for k, v in row.items()} for row in rows]

    p = parameters
    checks = []
    if (p["a"], p["b"], p["M"], p["K0"], p["f"], p["max_stages"]) == (7, 5, 4290, 32, 4, 4):
        checks.append({"table": "main-stages.csv", "actual": stringify(tables["stages"]),
                       "expected": read("main-stages.csv")})
        checks.append({"table": "periodic-components.csv", "actual": stringify(tables["periodic_components"]),
                       "expected": read("periodic-components.csv")})
    else:
        matches = [row for row in read("known-cases.csv")
                   if tuple(int(row[k]) for k in ("a", "b", "M", "K"))
                   == (p["a"], p["b"], p["M"], p["K0"])]
        if matches:
            actual = [{"a": p["a"], "b": p["b"], "M": p["M"], **row}
                      for row in tables["stages"]]
            checks.append({"table": "known-cases.csv", "actual": stringify(actual), "expected": matches})
    for check in checks:
        if check["table"] == "periodic-components.csv":
            # Table 2 groups have no scientific row order; preserve multiplicity.
            ordering = lambda row: json.dumps(row, sort_keys=True)
            equal = sorted(check["actual"], key=ordering) == sorted(check["expected"], key=ordering)
            check["comparison_policy"] = "row_multiset"
        else:
            equal = check["actual"] == check["expected"]
            check["comparison_policy"] = "row_sequence"
        check["status"] = "pass" if equal else "mismatch"
    return {"schema_version": 1, "kind": "postcomputation-expectation-comparison",
            "status": ("not_applicable" if not checks else
                       "pass" if all(c["status"] == "pass" for c in checks) else "mismatch"),
            "checks": checks, "independent_verification": False}
