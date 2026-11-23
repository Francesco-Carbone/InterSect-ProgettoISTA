"""Test della modifica CR3 - refactoring dei moduli helper (TC-39..TC-60).
Il refactoring non deve cambiare il comportamento. I test sono quindi di due tipi:
- TC-39 e TC-40 controllano il risultato della modifica (nessun nome usato dagli altri file e'
  sparito; le funzioni di utilita' hanno una sola definizione, in smt_utils.py);
- TC-41..TC-60 sono test di caratterizzazione delle funzioni unificate o spostate in
  smt_utils.py: gli output attesi sono stati ricavati eseguendo il codice PRIMA del
  refactoring, quindi descrivono il comportamento che non deve cambiare.
Non richiedono il solver: lavorano su file di testo e su CSV temporanei.
"""
import ast
from pathlib import Path

import numpy as np
import pandas as pd
import pytest

import smt_utils as sm
import solver_utils as su
import solver_utils_typed as st

ROOT = Path(__file__).resolve().parent.parent
MODULES = {"solver_utils": su, "solver_utils_typed": st, "smt_utils": sm}
MODULE_FILES = ("solver_utils.py", "solver_utils_typed.py", "smt_utils.py")
# funzioni e costanti spostate in smt_utils.py dalla CR3: devono avere una sola definizione
MOVED = ("_tokenize_smt2", "_get_command_name", "_strip_smt2_commands_2",
         "extract_free_vars_with_type_from_smt2_file", "uniform_multiset",
         "multiset_from_intervals_2", "expand_multiset", "index_to_string",
         "_format_literal", "_normalize_model_value", "_unescape_smt_string",
         "_normalize_mask_intervals")

SMT = (
    "(set-logic QF_LIA)\n"
    "(declare-fun x () Int)\n"
    "(declare-fun s () String)\n"
    "(declare-fun b () Bool)\n"
    "(assert (>= x 0))\n"
    "(check-sat)\n"
    "(get-model)\n"
)
L = [("x", "Int", 0, 10), ("s", "String", "a", "zz"), ("b", "Bool", None, None)]
FREE_VARS = [("x", "Int"), ("s", "String"), ("b", "Bool")]


class FakeZ3Value:
    """Valore di un modello: i moduli usano solo str(valore)."""

    def __init__(self, text):
        self.text = text

    def __str__(self):
        return self.text


def _file(tmp_path, text=SMT):
    path = tmp_path / "f.smt2"
    path.write_text(text)
    return path


# --------------------------------------------------------------------------- risultato della modifica
def _external_references():
    """(file, modulo, nome) per ogni nome che gli altri file prendono dai due moduli helper."""
    refs = []
    for folder in ("scripts", "tests", "system_tests"):
        for path in sorted((ROOT / folder).glob("*.py")):
            if path.name in MODULE_FILES:
                continue
            tree = ast.parse(path.read_text(encoding="utf-8"))
            alias = {}
            for node in ast.walk(tree):
                if isinstance(node, ast.ImportFrom) and node.module in MODULES:
                    refs += [(path.name, node.module, a.name) for a in node.names]
                elif isinstance(node, ast.Import):
                    for a in node.names:
                        if a.name in MODULES:
                            alias[a.asname or a.name] = a.name
                elif isinstance(node, ast.ImportFrom) and node.module in (None, "scripts"):
                    for a in node.names:
                        if a.name in MODULES:
                            alias[a.asname or a.name] = a.name
            for node in ast.walk(tree):
                if (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name)
                        and node.value.id in alias):
                    refs.append((path.name, alias[node.value.id], node.attr))
    return refs


def test_tc39_tutti_i_nomi_usati_dagli_altri_file_esistono_ancora():
    refs = _external_references()
    assert len(refs) > 30, "controllo troppo debole: pochi riferimenti trovati"
    missing = [r for r in refs if not hasattr(MODULES[r[1]], r[2])]
    assert not missing, missing


def _top_level_names(path):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    names = [n.name for n in tree.body if isinstance(n, ast.FunctionDef)]
    names += [t.id for n in tree.body if isinstance(n, ast.Assign)
              for t in n.targets if isinstance(t, ast.Name)]
    return names


def test_tc40_le_funzioni_di_utilita_hanno_una_sola_definizione_in_smt_utils():
    scripts = ROOT / "scripts"
    in_smt_utils = _top_level_names(scripts / "smt_utils.py")
    for name in MOVED:
        assert in_smt_utils.count(name) == 1, name
        for other in ("solver_utils.py", "solver_utils_typed.py"):
            assert name not in _top_level_names(scripts / other), (name, other)
    # i moduli che ne hanno bisogno le importano da smt_utils (stesso oggetto, nessuna copia)
    assert st.extract_free_vars_with_type_from_smt2_file is sm.extract_free_vars_with_type_from_smt2_file
    assert su.index_to_string is sm.index_to_string
    assert st._format_literal is sm._format_literal


# --------------------------------------------------------------------------- prevent_same_model_*
def test_tc41_prevent_same_model_typed_inserisce_il_blocco_prima_del_check_sat(tmp_path):
    path = _file(tmp_path)
    model = {"x": FakeZ3Value("7"), "s": FakeZ3Value('"hi"'), "b": FakeZ3Value("true")}
    st.prevent_same_model_typed(model, L, path)
    assert path.read_text() == (
        "(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun s () String)\n"
        "(declare-fun b () Bool)\n(assert (>= x 0))\n"
        '(assert (not (and (= x 7) (= s "hi") (= b true))))\n'
        "(check-sat)\n(get-model)\n"
    )


def test_tc42_prevent_same_model_typed_ignora_le_variabili_fuori_da_L(tmp_path):
    path = _file(tmp_path)
    st.prevent_same_model_typed({"zzz": FakeZ3Value("1")}, L, path)
    assert path.read_text() == SMT


def test_tc43_prevent_same_model_typed_senza_check_sat_aggiunge_in_coda(tmp_path):
    path = _file(tmp_path, "(declare-fun x () Int)\n")
    st.prevent_same_model_typed({"x": FakeZ3Value("-3")}, L, path)
    assert path.read_text() == "(declare-fun x () Int)\n(assert (not (and (= x -3))))\n"


def test_tc44_prevent_same_model_for_free_vars_scrive_lo_stesso_blocco(tmp_path):
    path = _file(tmp_path)
    model = {"x": FakeZ3Value("7"), "s": FakeZ3Value('"hi"'), "b": FakeZ3Value("false")}
    st.prevent_same_model_for_free_vars_typed(model, FREE_VARS, path)
    assert path.read_text() == (
        "(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun s () String)\n"
        "(declare-fun b () Bool)\n(assert (>= x 0))\n"
        '(assert (not (and (= x 7) (= s "hi") (= b false))))\n'
        "(check-sat)\n(get-model)\n"
    )


# --------------------------------------------------------------------------- add_e_assignment_typed
def test_tc45_add_e_assignment_typed_inserisce_prima_del_check_sat(tmp_path):
    path = _file(tmp_path)
    assignment = {
        "x": {"value": 5, "type": "Int"},
        "s": {"value": "q", "type": "String"},
        "b": {"value": True, "type": "Bool"},
    }
    st.add_e_assignment_typed(assignment, path)
    assert path.read_text() == (
        "(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun s () String)\n"
        "(declare-fun b () Bool)\n(assert (>= x 0))\n"
        '(assert (and\n    (= x 5)\n    (= s "q")\n    (= b true)\n))\n'
        "(check-sat)\n(get-model)\n"
    )


def test_tc46_add_e_assignment_typed_sostituisce_l_assegnamento_precedente(tmp_path):
    path = _file(
        tmp_path,
        "(declare-fun x () Int)\n(assert (and\n    (= x 3)\n))\n(check-sat)\n",
    )
    st.add_e_assignment_typed({"x": {"value": 9, "type": "Int"}}, path)
    assert path.read_text() == (
        "(declare-fun x () Int)\n(assert (and\n    (= x 9)\n))\n(check-sat)\n"
    )


def test_tc47_add_e_assignment_typed_senza_check_sat_aggiunge_in_coda(tmp_path):
    path = _file(tmp_path, "(declare-fun x () Int)\n")
    st.add_e_assignment_typed({"x": {"value": 9, "type": "Int"}}, path)
    assert path.read_text() == "(declare-fun x () Int)\n(assert (and\n    (= x 9)\n))\n"


# --------------------------------------------------------------------------- scrittura dei CSV
def _benchmark(tmp_path):
    bench = tmp_path / "bench"
    bench.mkdir()
    smt = bench / "a.smt2"
    smt.write_text("x")
    return smt


def _csvs(tmp_path):
    return sorted(str(p.relative_to(tmp_path)).replace("\\", "/") for p in tmp_path.rglob("*.csv"))


def test_tc48_scrittura_csv_dei_risultati_nella_cartella_con_cov_e_strlen(tmp_path):
    smt = _benchmark(tmp_path)
    rows = {"status": ["SAT", "UNSAT"], "time": [1.5, 2.5]}
    st._write_solver_results_typed(rows, str(smt), 50, 54, results_suffix="_x")
    assert _csvs(tmp_path) == ["bench_results_x_cov50_strlen54/a.csv"]
    saved = pd.read_csv(tmp_path / "bench_results_x_cov50_strlen54" / "a.csv")
    assert saved["status"].tolist() == ["SAT", "UNSAT"]


def test_tc49_scrittura_csv_senza_suffisso_strlen_e_con_nome_forzato_csv(tmp_path):
    smt = _benchmark(tmp_path)
    st._write_solver_results_typed(
        {"status": ["SAT"]}, str(smt), 10, 8,
        output_filename="out.txt", include_string_length_suffix=False,
    )
    assert _csvs(tmp_path) == ["bench_results_cov10/out.csv"]


def test_tc50_scrittura_csv_baseline_e_percorso_di_lettura_coincidono(tmp_path):
    smt = _benchmark(tmp_path)
    st._write_baseline_solver_results_typed({"status": ["SAT"]}, str(smt), results_suffix="_b")
    assert _csvs(tmp_path) == ["bench_results_b/a.csv"]
    expected = tmp_path / "bench_results_b" / "a.csv"
    assert st._baseline_result_csv_path(str(smt), "_b") == expected
    assert expected.exists()


# --------------------------------------------------------------------------- funzioni di smt_utils.py
def test_tc51_strip_smt2_commands_tiene_solo_i_comandi_accettati_da_z3():
    smt = (
        "(set-logic QF_LIA)\n(set-info :status sat)\n(declare-fun x () Int)\n"
        "(declare-const y (_ BitVec 8))\n(push 1)\n(assert (>= x 0)) ; commento (con parentesi\n"
        "(check-sat)\n(pop 1)\n(get-model)\n"
    )
    assert sm._strip_smt2_commands_2(smt) == (
        "(set-logic QF_LIA)\n(declare-fun x () Int)\n"
        "(declare-const y (_ BitVec 8))\n(assert (>= x 0))"
    )


def test_tc52_tokenizer_gestisce_stringhe_simboli_quotati_e_commenti():
    assert sm._tokenize_smt2('(a (b "c)") |d)| ; e\n) f') == ['(a (b "c)") |d)| ; e\n)', "f"]
    assert sm._get_command_name("(Declare-Fun x") == "declare-fun"
    assert sm._get_command_name("x") is None


def test_tc53_extract_free_vars_with_type_legge_declare_fun_e_declare_const(tmp_path):
    path = _file(
        tmp_path,
        "(declare-fun x () Int)\n(declare-const y (_ BitVec 8))\n"
        "(declare-fun f (Int) Int)\n(declare-fun s () String)\n(assert true)\n",
    )
    assert sm.extract_free_vars_with_type_from_smt2_file(path) == [
        ("x", "Int"), ("y", "(_ BitVec 8)"), ("s", "String"),
    ]


def test_tc54_format_literal_per_ogni_tipo():
    assert [sm._format_literal(v, t) for v, t in [
        (True, "Bool"), (False, "Bool"), (5, "(_ BitVec 8)"), ('a"b\\c', "String"), (-3, "Int"),
    ]] == ["true", "false", "(_ bv5 8)", '"a\\"b\\\\c"', "-3"]


def test_tc55_normalize_model_value_e_unescape():
    assert [sm._normalize_model_value(FakeZ3Value(v), t) for v, t in [
        ('"hi"', "String"), ("ab", "String"), ("true", "Bool"), ("false", "Bool"), ("-7", "Int"),
    ]] == ["hi", "ab", True, False, -7]
    assert sm._unescape_smt_string("a\\nb\\x41") == "a\nbA"


def test_tc56_normalize_mask_intervals_taglia_ordina_e_fonde():
    assert sm._normalize_mask_intervals([(5, 9), (0, 3), (2, 4), (8, 20), (30, 40), (7, 7)], 1, 15) == [(1, 4), (5, 15)]
    assert sm._normalize_mask_intervals([], 0, 5) == []
    assert sm._normalize_mask_intervals([(10, 12)], 0, 5) == []


def test_tc57_index_to_string_segue_l_ordine_lessicografico():
    assert [sm.index_to_string(i) for i in (0, 25, 26, 27, 51, 52, 701, 702)] == [
        "a", "z", "aa", "ab", "az", "ba", "zz", "aaa",
    ]
    assert sm.index_to_string(sm.TOTAL_STRINGS + 3) == "d"


def test_tc58_index_to_string_rifiuta_gli_indici_negativi():
    with pytest.raises(ValueError, match="non-negative"):
        sm.index_to_string(-1)


def test_tc59_multiset_from_intervals_conta_i_campioni_del_dominio_normalizzato():
    full = sm.multiset_from_intervals_2([(0, 10), (10, 20)], 0, 100)
    assert sum(full.values()) == 200 and len(full) == 199
    assert sorted(full)[:2] == pytest.approx([0.0, 0.001010101010101])
    single = sm.multiset_from_intervals_2([(5, 5)], 0, 100)
    assert list(single) == pytest.approx([0.05]) and list(single.values()) == [5]


def test_tc60_expand_e_uniform_multiset():
    from collections import Counter
    assert sm.expand_multiset(Counter({0.5: 2, 0.25: 1})).tolist() == [0.5, 0.5, 0.25]
    np.random.seed(3)
    uniform = sm.uniform_multiset(0, 10, 5)
    assert sm.expand_multiset(uniform).tolist() == [0.550798, 0.708148, 0.290905, 0.510828, 0.892947]
