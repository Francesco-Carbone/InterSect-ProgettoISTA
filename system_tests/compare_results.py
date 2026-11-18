"""
Confronto tra due campagne di system test.

    python system_tests/compare_results.py baseline after_CR
    python system_tests/compare_results.py baseline after_CR --verify

Per ogni file e per ogni campagna calcola (media/min/max sulle run):
SAT, UNSAT, UNKNOWN, modelli SAT distinti, tempo totale del solver.
Con --verify controlla anche che ogni modello SAT soddisfi la formula
ORIGINALE (indipendente dal sampler). Verifica solo variabili Int/BitVec/Bool.
"""
import argparse
import re
import sys
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "system_tests"
META = {"status", "mask_var_pairs", "mask_bounds", "time"}


def original_smt(csv_path, bench_root):
    bench = csv_path.parent.name.split("_results")[0]
    return bench_root / bench / (csv_path.stem + ".smt2")


def literal(value, typ):
    v = str(value).strip()
    if typ == "Bool":
        return "true" if v.lower() == "true" else "false"
    m = re.match(r"^\(_\s+BitVec\s+(\d+)\)$", typ)
    if m:
        return f"(_ bv{int(v)} {m.group(1)})"
    n = int(v)  # Int
    return str(n) if n >= 0 else f"(- {-n})"


def verify_file(csv_path, df, bench_root, max_rows):
    """Ritorna (verificati, validi, nota)."""
    import z3
    from scripts.solver_utils import _strip_smt2_commands_2
    from scripts.solver_utils_typed import extract_free_vars_with_type_from_smt2_file

    smt = original_smt(csv_path, bench_root)
    if not smt.exists():
        return 0, 0, f"originale non trovato: {smt}"
    types = dict(extract_free_vars_with_type_from_smt2_file(smt))
    if any(t == "String" for t in types.values()):
        return 0, 0, "variabili String: verifica non supportata"
    base = _strip_smt2_commands_2(smt.read_text())
    sat = df[df["status"].str.upper() == "SAT"].head(max_rows)
    ok = 0
    for _, row in sat.iterrows():
        extra = []
        for name, typ in types.items():
            if name in row and pd.notna(row[name]):
                extra.append(f"(assert (= {name} {literal(row[name], typ)}))")
        s = z3.Solver()
        s.add(z3.parse_smt2_string(base + "\n" + "\n".join(extra)))
        ok += s.check() == z3.sat
    return len(sat), ok, ""


def collect(label, verify, bench_root, max_rows):
    rows = []
    for run_dir in sorted((OUT / label).glob("run*")):
        for csv_path in run_dir.rglob("*.csv"):
            df = pd.read_csv(csv_path, dtype=str)
            status = df["status"].str.upper()
            var_cols = [c for c in df.columns if c not in META]
            sat = df[status == "SAT"]
            t = pd.to_numeric(df["time"], errors="coerce")
            r = {
                "label": label, "run": run_dir.name, "file": csv_path.stem,
                "n_sat": int((status == "SAT").sum()),
                "n_unsat": int((status == "UNSAT").sum()),
                "n_unknown": int((status == "UNKNOWN").sum()),
                "distinct_sat": int(sat[var_cols].drop_duplicates().shape[0]),
                "time_total": float(t.sum()),
            }
            if verify:
                n, ok, note = verify_file(csv_path, df, bench_root, max_rows)
                r["verified"], r["valid"], r["note"] = n, ok, note
            rows.append(r)
    return rows


def main():
    p = argparse.ArgumentParser()
    p.add_argument("baseline")
    p.add_argument("after")
    p.add_argument("--verify", action="store_true")
    p.add_argument("--verify-max", type=int, default=50, help="max modelli verificati per file")
    p.add_argument("--bench-root", default=str(ROOT / "benchmarks"))
    a = p.parse_args()

    rows = []
    for label in (a.baseline, a.after):
        rows += collect(label, a.verify, Path(a.bench_root), a.verify_max)
    if not rows:
        sys.exit("Nessun CSV trovato in system_tests/")
    df = pd.DataFrame(rows)
    df.to_csv(OUT / f"all_runs_{a.baseline}_vs_{a.after}.csv", index=False)

    agg = df.groupby(["file", "label"]).agg(
        runs=("run", "count"),
        sat_mean=("n_sat", "mean"), sat_min=("n_sat", "min"), sat_max=("n_sat", "max"),
        unsat=("n_unsat", "mean"), unknown=("n_unknown", "mean"),
        distinct=("distinct_sat", "mean"),
        time_mean=("time_total", "mean"), time_min=("time_total", "min"),
        time_max=("time_total", "max"),
    ).round(2)
    print(agg.to_string())
    agg.to_csv(OUT / f"comparison_{a.baseline}_vs_{a.after}.csv")

    if a.verify:
        v = df.groupby(["file", "label"])[["verified", "valid"]].sum()
        print("\nVerifica modelli SAT sulla formula originale (validi / verificati):")
        print(v.to_string())
        notes = df[df["note"] != ""][["label", "file", "note"]].drop_duplicates()
        if not notes.empty:
            print("\nNote:\n" + notes.to_string(index=False))


if __name__ == "__main__":
    main()
