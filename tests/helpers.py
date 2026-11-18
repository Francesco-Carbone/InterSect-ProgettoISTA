"""Funzioni di supporto comuni ai test di InterSect (TC-01 ... TC-30)."""
import csv
import random
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

# ---------------------------------------------------------------------------
# File SMT di test (F1 ... F9, vedi Test Case Specification, Tabella 3)
# ---------------------------------------------------------------------------
def _smt(declarations, assertions, logic="QF_LIA"):
    lines = [f"(set-logic {logic})"]
    lines += declarations
    lines += [f"(assert {a})" for a in assertions]
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


FIXTURES = {
    "f1": _smt(
        ["(declare-fun x () Int)", "(declare-fun y () Int)"],
        ["(>= x 0)", "(<= x 2)", "(>= y 0)", "(<= y 2)", "(< x y)"],
    ),
    "f2": _smt(
        ["(declare-fun u () Int)", "(declare-fun v () Int)"],
        ["(>= u 0)", "(<= u 100000)", "(>= v 0)", "(<= v 100000)", "(< u v)"],
    ),
    "f3": _smt(
        ["(declare-fun x () Int)", "(declare-fun u () Int)"],
        ["(>= x 0)", "(<= x 2)", "(>= u 0)", "(<= u 100000)", "(< x u)"],
    ),
    "f4": _smt(
        ["(declare-fun u () Int)"],
        ["(>= u 0)", "(<= u 100000)", "(= (+ u 1) u)"],
    ),
    "f5": _smt(
        ["(declare-fun b () (_ BitVec 16))"],
        ["(bvult b (_ bv60000 16))"],
        logic="QF_BV",
    ),
    "f6": _smt(
        ["(declare-fun s () String)"],
        ["(<= (str.len s) 3)"],
        logic="QF_S",
    ),
    "f7": _smt(["(declare-fun r () Real)"], ["(> r 1.0)"], logic="QF_LRA"),
    "f8": _smt(["(declare-fun u () Int)"], ["(>= u 10)", "(<= u 5)"]),
    "f9": _smt(["(declare-fun u () Int)"], ["(>= u 5)", "(<= u 5)"]),
}


def write_fixture(directory, name):
    """Scrive il file SMT <name>.smt2 in <directory> e ne restituisce il percorso."""
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{name}.smt2"
    path.write_text(FIXTURES[name])
    return path


# ---------------------------------------------------------------------------
# Lettura dei risultati
# ---------------------------------------------------------------------------
def results_dir(results_root, smt_path, coverage=50, suffix="_interval_guided_sampler"):
    smt_path = Path(smt_path)
    return Path(results_root) / f"{smt_path.parent.name}_results{suffix}_cov{coverage}"


def csv_path(results_root, smt_path, name=None):
    """Percorso del CSV prodotto da intervalGuidedSampler."""
    smt_path = Path(smt_path)
    filename = name if name is not None else smt_path.stem + ".csv"
    return results_dir(results_root, smt_path) / filename


def read_rows(path):
    with open(path, newline="") as handle:
        return list(csv.DictReader(handle))


def count_status(rows, status):
    return sum(1 for row in rows if str(row.get("status", "")).strip().upper() == status)


def to_int(value):
    """Converte un valore di modello (int, stringa decimale o esadecimale) in int."""
    if isinstance(value, int):
        return value
    text = str(value).strip()
    if text.startswith("#x"):
        return int(text[2:], 16)
    if text.startswith("#b"):
        return int(text[2:], 2)
    return int(text)


def model_dict(model):
    """Un elemento di S (frozenset di coppie nome-valore) come dizionario."""
    return dict(model)


# ---------------------------------------------------------------------------
# Maschere: generatori casuali e proprieta' P1-P4
# ---------------------------------------------------------------------------
def seed_all(value):
    random.seed(value)
    np.random.seed(value)


def mask_properties(mask, min_value, max_value, target_coverage):
    """Ritorna le proprieta' P1-P4 del Test Case Specification per una maschera."""
    p1 = all(mask[i][0] <= mask[i + 1][0] for i in range(len(mask) - 1))
    p2 = all(mask[i][1] < mask[i + 1][0] for i in range(len(mask) - 1))
    p3 = all(min_value <= start <= end <= max_value for start, end in mask)
    coverage = sum(end - start for start, end in mask) / (max_value - min_value) * 100
    p4 = abs(coverage - target_coverage) <= 2
    return {"P1": p1, "P2": p2, "P3": p3, "P4": p4}, coverage
