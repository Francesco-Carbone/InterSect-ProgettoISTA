"""
Confronto della sequenza di campioni tra due campagne (test di regressione di un refactoring).

Un refactoring non deve cambiare il comportamento: con --threads 1, --seed fisso e
PYTHONHASHSEED=0 (vedi ST-R2 in run_optional_tests.py) lo stesso codice produce la stessa
sequenza di campioni e di maschere. Questo script confronta il CSV di una campagna di
riferimento (eseguita PRIMA della modifica) con quello di una campagna eseguita DOPO.

Esempio dalla radice del progetto, su Windows PowerShell:

    $env:PYTHONHASHSEED = "0"
    python system_tests/run_system_tests.py --label st_r2_dopo_CR3 --runs 1 `
        --files benchmarks/slacks-80/10-12.slack.smt2 `
        --threads 1 --seed 1 --num-samples 20 --timeout 120
    python system_tests/compare_sequences.py st_r2_a st_r2_dopo_CR3

La colonna 'time' non si confronta. Se le due run si fermano a righe diverse (timeout) si
confronta il prefisso comune, che deve contenere almeno --min-rows righe.

Exit code 0 se la sequenza coincide, 1 altrimenti.
"""
import argparse
import sys
from pathlib import Path

import pandas as pd

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "system_tests"
DEFAULT_FILE = "benchmarks/slacks-80/10-12.slack.smt2"


def find_csv(label, file):
    hits = sorted((OUT / label / "run1").rglob(Path(file).stem + ".csv"))
    return hits[0] if hits else None


def load(label, file):
    path = find_csv(label, file)
    if path is None:
        sys.exit(f"nessun CSV per {Path(file).stem} nella campagna {label} (cartella {OUT / label})")
    df = pd.read_csv(path, dtype=str).drop(columns=["time"], errors="ignore")
    return df.fillna("<NA>").reset_index(drop=True)


def _short(value, head=40, tail=15):
    """Valore abbreviato: inizio e fine, perche' i numeri lunghi differiscono spesso in coda."""
    value = str(value)
    return repr(value) if len(value) <= head + tail else f"{value[:head]!r}...{value[-tail:]!r} (len {len(value)})"


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("reference", help="etichetta della campagna di riferimento (prima della modifica)")
    p.add_argument("candidate", help="etichetta della campagna da verificare (dopo la modifica)")
    p.add_argument("--file", default=DEFAULT_FILE)
    p.add_argument("--min-rows", type=int, default=5)
    a = p.parse_args()

    A, B = load(a.reference, a.file), load(a.candidate, a.file)
    print(f"righe: {a.reference}={len(A)}, {a.candidate}={len(B)}")
    if set(A.columns) != set(B.columns):
        print("FAIL: colonne diverse tra le due campagne")
        print(f"   solo in {a.reference}: {sorted(set(A.columns) - set(B.columns))}")
        print(f"   solo in {a.candidate}: {sorted(set(B.columns) - set(A.columns))}")
        return 1
    B = B[A.columns]

    n = min(len(A), len(B))
    if n < a.min_rows:
        print(f"NON CONCLUSIVO: righe confrontabili ({n}) < minimo ({a.min_rows}); aumenta --timeout")
        return 1
    diff = (A.head(n) != B.head(n)).any(axis=1)
    print(f"righe confrontate (prefisso comune): {n}")
    if diff.any():
        i = int(diff.idxmax())
        cols = [c for c in A.columns if A.at[i, c] != B.at[i, c]]
        print(f"FAIL: prima divergenza alla riga {i}, colonne: {cols}")
        for c in cols[:3]:
            print(f"   {c}: {_short(A.at[i, c])} vs {_short(B.at[i, c])}")
        return 1
    print("PASS: sequenza di campioni e maschere identica")
    return 0


if __name__ == "__main__":
    sys.exit(main())
