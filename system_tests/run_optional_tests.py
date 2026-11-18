"""
Casi di test opzionali del system test (TPS Test System):

  ST-R2  Riproducibilità: due esecuzioni con --threads 1 --seed 1 devono
         produrre la stessa sequenza di campioni.
  ST-R3  Timeout: con --timeout 60 --grace 30 il worker deve fermarsi entro
         90 s; se supera il limite, summary.csv deve riportare timed_out=True.

Va messo nella stessa cartella di run_system_tests.py (system_tests/).
Dalla radice del progetto:

    python system_tests/run_optional_tests.py r2
    python system_tests/run_optional_tests.py r3
    python system_tests/run_optional_tests.py all

Exit code 0 se tutti i test eseguiti passano, 1 altrimenti.
"""
import argparse
import csv
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pandas as pd

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OUT = ROOT / "system_tests"
RUNNER = HERE / "run_system_tests.py"
DEFAULT_FILE = "benchmarks/slacks-80/10-12.slack.smt2"


# ---------------------------------------------------------------- utilità
def run_campaign(label, file, extra_args, env):
    """Lancia run_system_tests.py su un solo file con una label dedicata."""
    shutil.rmtree(OUT / label, ignore_errors=True)  # niente CSV vecchi (il sampler appende)
    cmd = [sys.executable, str(RUNNER), "--label", label, "--runs", "1",
           "--files", file] + extra_args
    print("\n$ " + " ".join(cmd))
    subprocess.run(cmd, cwd=ROOT, env=env)


def read_summary(label):
    path = OUT / label / "summary.csv"
    if not path.exists():
        return None
    with path.open(newline="") as fh:
        rows = list(csv.DictReader(fh))
    return rows[-1] if rows else None


def find_csv(label, file):
    hits = sorted((OUT / label / "run1").rglob(Path(file).stem + ".csv"))
    return hits[0] if hits else None


def verdict(name, ok, details):
    print(f"\n[{name}] {'PASS' if ok else 'FAIL'}")
    for d in details:
        print("   - " + d)
    return ok


# ---------------------------------------------------------------- ST-R2
def st_r2(a):
    env = os.environ.copy()
    if not a.no_hashseed:
        # L ed E sono set di tuple con stringhe: senza hash seed fisso l'ordine
        # di iterazione (quindi l'ordine di consumo dei numeri casuali) cambia
        # da un processo all'altro, anche con lo stesso --seed.
        env["PYTHONHASHSEED"] = "0"

    common = ["--threads", "1", "--seed", str(a.seed),
              "--num-samples", str(a.num_samples), "--timeout", str(a.timeout)]
    labels = ["st_r2_a", "st_r2_b"]
    for label in labels:
        run_campaign(label, a.file, common, env)

    frames = []
    for label in labels:
        path = find_csv(label, a.file)
        if path is None:
            return verdict("ST-R2", False, [f"nessun CSV prodotto da {label}"])
        df = pd.read_csv(path, dtype=str).drop(columns=["time"], errors="ignore")
        frames.append(df.fillna("<NA>").reset_index(drop=True))
    A, B = frames

    details = [f"righe: {labels[0]}={len(A)}, {labels[1]}={len(B)} "
               f"(PYTHONHASHSEED={'non fissato' if a.no_hashseed else '0'})"]
    if set(A.columns) != set(B.columns):
        return verdict("ST-R2", False, details + ["colonne diverse tra le due esecuzioni"])
    B = B[A.columns]

    # Con un timeout temporale le due run possono fermarsi a righe diverse:
    # si confronta il prefisso comune (la colonna 'time' è esclusa).
    n = min(len(A), len(B))
    if n < a.min_rows:
        return verdict("ST-R2", False,
                       details + [f"righe confrontabili ({n}) < minimo ({a.min_rows}): "
                                  "test non conclusivo, aumenta --timeout"])
    diff = (A.head(n) != B.head(n)).any(axis=1)
    details.append(f"righe confrontate (prefisso comune): {n}")
    if diff.any():
        i = int(diff.idxmax())
        cols = [c for c in A.columns if A.at[i, c] != B.at[i, c]]
        details.append(f"prima divergenza alla riga {i}, colonne: {cols}")
        for c in cols[:3]:
            details.append(f"  {c}: {str(A.at[i, c])[:70]!r} vs {str(B.at[i, c])[:70]!r}")
        return verdict("ST-R2", False, details)
    return verdict("ST-R2", True, details + ["sequenza di campioni e maschere identica"])


# ---------------------------------------------------------------- ST-R3
def r3_case(name, label, a, timeout, grace, expect_hard_kill):
    env = os.environ.copy()
    extra = ["--threads", str(a.threads), "--seed", str(a.seed),
             "--num-samples", "1000000",  # non deve essere il num_samples a fermare la run
             "--timeout", str(timeout), "--grace", str(grace)]
    run_campaign(label, a.file, extra, env)

    row = read_summary(label)
    if row is None:
        return verdict(name, False, ["summary.csv assente o vuoto"])

    limit = timeout + grace
    wall = float(row["wall_s"])
    timed_out = row["timed_out"].strip().lower() == "true"
    code = int(row["exit_code"])
    ok, d = True, [f"limite duro = {limit} s, tempo misurato = {wall:.1f} s, "
                   f"timed_out={timed_out}, exit_code={code}"]

    if expect_hard_kill:
        ok &= timed_out and code == -1 and limit - 1 <= wall <= limit + 15
        d.append("atteso: timed_out=True, exit_code=-1, stop intorno al limite duro")
    elif timed_out:
        ok &= code == -1 and wall >= limit - 1
        d.append("il worker ha superato il limite: kill duro registrato correttamente")
    else:
        within = code == 0 and wall <= limit + 5
        ok &= within
        if not within:
            d.append("il worker è finito oltre il limite duro senza essere registrato "
                     "come timed_out, oppure con exit_code diverso da 0")
        elif wall < timeout - 5:
            d.append("il sampler è terminato da solo prima del timeout: "
                     "percorso di timeout non esercitato (usa un benchmark più lungo)")
        else:
            d.append("stop morbido interno entro il limite duro")

    csv_path = find_csv(label, a.file)
    if csv_path is not None:
        try:
            d.append(f"CSV parziale leggibile: {len(pd.read_csv(csv_path, dtype=str))} righe")
        except Exception as exc:  # file troncato dal kill
            ok = False
            d.append(f"CSV illeggibile dopo l'interruzione: {exc}")
    else:
        d.append("nessun CSV (nessuna soluzione salvata prima dell'interruzione)")
    return verdict(name, ok, d)


def st_r3(a):
    ok_a = r3_case("ST-R3a (specifica: --timeout 60 --grace 30)", "st_r3_soft", a,
                   timeout=60, grace=30, expect_hard_kill=False)
    # Forza il kill duro: timeout interno enorme, limite duro = 3600 - 3540 = 60 s.
    ok_b = r3_case("ST-R3b (kill duro forzato)", "st_r3_hard", a,
                   timeout=3600, grace=-3540, expect_hard_kill=True)
    print("\nNota: su Windows il kill del worker può lasciare processi figli del pool "
          "attivi; controlla Gestione attività prima di rilanciare.")
    return ok_a and ok_b


# ---------------------------------------------------------------- main
def main():
    p = argparse.ArgumentParser()
    p.add_argument("which", choices=["r2", "r3", "all"])
    p.add_argument("--file", default=DEFAULT_FILE)
    p.add_argument("--seed", type=int, default=1)
    # ST-R2
    p.add_argument("--num-samples", type=int, default=20)
    p.add_argument("--timeout", type=int, default=120, help="timeout di ogni run di ST-R2")
    p.add_argument("--min-rows", type=int, default=5)
    p.add_argument("--no-hashseed", action="store_true",
                   help="non fissare PYTHONHASHSEED (verifica la non-determinazione dei set)")
    # ST-R3
    p.add_argument("--threads", type=int, default=60)
    a = p.parse_args()

    if not RUNNER.exists():
        sys.exit(f"run_system_tests.py non trovato in {HERE}")

    results = []
    if a.which in ("r2", "all"):
        results.append(st_r2(a))
    if a.which in ("r3", "all"):
        results.append(st_r3(a))
    sys.exit(0 if all(results) else 1)


if __name__ == "__main__":
    main()