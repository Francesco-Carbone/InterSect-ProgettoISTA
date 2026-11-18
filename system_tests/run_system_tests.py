"""
Campagna di system test per intervalGuidedSampler.

Esempi (dalla radice del progetto o da qualsiasi cartella):
    python system_tests/run_system_tests.py --label baseline --runs 2
    python system_tests/run_system_tests.py --label after_CR --runs 2

Ogni file di benchmark viene eseguito in un processo separato, quindi un crash
di un file non blocca la campagna. I CSV finiscono in
    system_tests/<label>/run<k>/...
e il riepilogo (exit code, tempo) in system_tests/<label>/summary.csv.
"""
import argparse
import csv
import random
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "system_tests"

DEFAULT_FILES = [
    "benchmarks/slacks-80/10-12.slack.smt2",
    "benchmarks/slacks-80/10-13.slack.smt2",
    "benchmarks/slacks-80/10-20.slack.smt2",
    "benchmarks/slacks-80/10-21.slack.smt2",
    "benchmarks/slacks-80/10-28.slack.smt2",
]


def resolve(p):
    p = Path(p)
    return p if p.is_absolute() else ROOT / p


def run_worker(a):
    import numpy as np


    scripts_dir = str(ROOT / "scripts")
    if scripts_dir not in sys.path:
        sys.path.insert(0, scripts_dir)

    from solver_utils_typed import intervalGuidedSampler

    random.seed(a.seed)
    np.random.seed(a.seed)
    intervalGuidedSampler(
        str(resolve(a.file)),
        theta=a.theta,
        coverage=a.coverage,
        delta=a.delta,
        U=2**256 - 1,
        timeout=a.timeout,
        threads=a.threads,
        num_samples=a.num_samples,
        results_root=a.results_root,
    )


def clean_tmp():
    for f in (ROOT / "tmp").glob("tmp_*.smt2"):
        f.unlink(missing_ok=True)


def run_campaign(a):
    label_dir = OUT / a.label
    label_dir.mkdir(parents=True, exist_ok=True)
    summary = label_dir / "summary.csv"
    new = not summary.exists()
    with summary.open("a", newline="") as fh:
        w = csv.writer(fh)
        if new:
            w.writerow(["run", "file", "exit_code", "timed_out", "wall_s"])
        for k in range(1, a.runs + 1):
            run_root = label_dir / f"run{k}"
            for file in a.files:
                if not resolve(file).exists():
                    print(f"[SKIP] file non trovato: {file}")
                    continue
                cmd = [
                    sys.executable, str(Path(__file__).resolve()), "--worker",
                    "--file", file, "--results-root", str(run_root),
                    "--seed", str(a.seed), "--theta", str(a.theta),
                    "--coverage", str(a.coverage), "--delta", str(a.delta),
                    "--timeout", str(a.timeout), "--num-samples", str(a.num_samples),
                ]
                if a.threads is not None:
                    cmd += ["--threads", str(a.threads)]
                print(f"[RUN {k}/{a.runs}] {file}")
                t0 = time.perf_counter()
                timed_out = False
                try:
                    # margine: una singola chiamata a z3 non viene interrotta dal timeout interno
                    r = subprocess.run(cmd, cwd=ROOT, timeout=a.timeout + a.grace)
                    code = r.returncode
                except subprocess.TimeoutExpired:
                    timed_out, code = True, -1
                wall = time.perf_counter() - t0
                w.writerow([k, file, code, timed_out, round(wall, 2)])
                fh.flush()
                print(f"        exit={code} timeout_duro={timed_out} tempo={wall:.1f}s")
                clean_tmp()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--label", help="nome campagna, es. baseline / after_CR")
    p.add_argument("--files", nargs="*", default=DEFAULT_FILES)
    p.add_argument("--runs", type=int, default=1)
    p.add_argument("--num-samples", type=int, default=50, help="stop dopo N soluzioni SAT")
    p.add_argument("--timeout", type=int, default=1800)
    p.add_argument("--grace", type=int, default=600, help="secondi extra prima del kill")
    p.add_argument("--threads", type=int, default=60,
                   help="1 = generazione maschere in-process (seed rispettato)")
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--theta", type=int, default=256)
    p.add_argument("--coverage", type=int, default=50)
    p.add_argument("--delta", type=float, default=0.0050)
    # usati solo internamente dal processo figlio
    p.add_argument("--worker", action="store_true")
    p.add_argument("--file")
    p.add_argument("--results-root")
    a = p.parse_args()

    if a.worker:
        run_worker(a)
    else:
        if not a.label:
            p.error("--label è obbligatorio")
        run_campaign(a)


if __name__ == "__main__":
    main()
