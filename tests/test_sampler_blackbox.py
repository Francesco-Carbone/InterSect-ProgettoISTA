"""Test black box TM-01 (TC-01..TC-21) su intervalGuidedSampler.

Richiedono z3-solver installato. TC-06 e TC-07 sono attesi FALLIRE: documentano
l'incidente "doppia chiamata al solver con E e L vuoti" (requisito R9).
"""
import _thread
import threading

import pytest

import solver_utils_typed as st
from helpers import count_status, csv_path, read_rows

run = st.intervalGuidedSampler


def _csv(res_root, smt, name=None):
    return csv_path(res_root, smt, name)


# --------------------------------------------------------------- classi valide
def test_tc01_default_su_f1(fixture_file, res_root):
    smt = fixture_file("f1")
    S = run(str(smt), results_root=str(res_root))
    rows = read_rows(_csv(res_root, smt))
    assert len(S) == 3
    assert len(rows) == 9
    assert count_status(rows, "SAT") == 3
    assert count_status(rows, "UNSAT") == 6


def test_tc02_free_vars_timeout_num_samples_output(fixture_file, res_root):
    smt = fixture_file("f2")
    S = run(str(smt), free_vars=["u", "v"], timeout=600, num_samples=5,
            output_filename="out.csv", results_root=str(res_root))
    rows = read_rows(_csv(res_root, smt, "out.csv"))
    assert count_status(rows, "SAT") == 5
    assert len(S) == 5


def test_tc03_dominio_misto_output_senza_estensione(fixture_file, res_root):
    smt = fixture_file("f3")
    run(str(smt), num_samples=4, output_filename="mix", results_root=str(res_root))
    path = _csv(res_root, smt, "mix.csv")
    assert path.exists()
    assert count_status(read_rows(path), "SAT") == 4


def test_tc04_theta_piccola_su_f1(fixture_file, res_root):
    smt = fixture_file("f1")
    run(str(smt), theta=4, results_root=str(res_root))
    rows = read_rows(_csv(res_root, smt))
    assert len(rows) == 4


def test_tc05_formula_insoddisfacibile(fixture_file, res_root):
    smt = fixture_file("f4")
    S = run(str(smt), results_root=str(res_root))
    rows = read_rows(_csv(res_root, smt))
    assert len(S) == 0
    assert len(rows) == 20
    assert count_status(rows, "UNSAT") == 20


# ---- TC-06/TC-07: attesi in FALLIMENTO (R9: una sola chiamata, il codice ne fa due)
@pytest.mark.xfail(reason="INC-02: con E e L vuoti il solver e' invocato due volte", strict=False)
def test_tc06_free_vars_vuoto(fixture_file, res_root):
    smt = fixture_file("f1")
    run(str(smt), free_vars=[], results_root=str(res_root))
    assert len(read_rows(_csv(res_root, smt))) == 1


@pytest.mark.xfail(reason="INC-02: con E e L vuoti il solver e' invocato due volte", strict=False)
def test_tc07_tipo_non_gestito_real(fixture_file, res_root):
    smt = fixture_file("f7")
    run(str(smt), results_root=str(res_root))
    assert len(read_rows(_csv(res_root, smt))) == 1


# --------------------------------------------------------------- classi invalide
def test_tc08_file_inesistente(smt_dir, res_root):
    with pytest.raises(FileNotFoundError):
        run(str(smt_dir / "non_esiste.smt2"), results_root=str(res_root))


def test_tc09_timeout_negativo(fixture_file, res_root):
    with pytest.raises(ValueError):
        run(str(fixture_file("f1")), timeout=-1, results_root=str(res_root))


def test_tc10_timeout_stringa(fixture_file, res_root):
    with pytest.raises(TypeError):
        run(str(fixture_file("f1")), timeout="10", results_root=str(res_root))


def test_tc11_timeout_zero(fixture_file, res_root):
    smt = fixture_file("f1")
    S = run(str(smt), timeout=0, results_root=str(res_root))
    assert len(S) == 0
    assert not _csv(res_root, smt).exists()


def test_tc12_num_samples_zero(fixture_file, res_root):
    with pytest.raises(ValueError):
        run(str(fixture_file("f1")), num_samples=0, results_root=str(res_root))


def test_tc13_num_samples_non_intero(fixture_file, res_root):
    with pytest.raises(TypeError):
        run(str(fixture_file("f1")), num_samples=2.5, results_root=str(res_root))


# --------------------------------------------------------------- num_samples / ripresa
def test_tc14_num_samples_uno(fixture_file, res_root):
    smt = fixture_file("f1")
    run(str(smt), num_samples=1, results_root=str(res_root))
    assert count_status(read_rows(_csv(res_root, smt)), "SAT") == 1


def test_tc15_csv_preesistente_gia_sufficiente(fixture_file, res_root):
    smt = fixture_file("f1")
    path = _csv(res_root, smt)
    path.parent.mkdir(parents=True, exist_ok=True)
    content = "status,x,y\nSAT,0,1\nSAT,0,2\n"
    path.write_text(content)
    S = run(str(smt), num_samples=2, results_root=str(res_root))
    assert len(S) == 0
    assert path.read_text() == content


def test_tc16_ripresa_da_csv_precedente(fixture_file, res_root):
    smt = fixture_file("f1")
    run(str(smt), num_samples=1, results_root=str(res_root))
    S = run(str(smt), num_samples=3, results_root=str(res_root))
    assert len(S) == 2
    assert count_status(read_rows(_csv(res_root, smt)), "SAT") == 3


# --------------------------------------------------------------- domini limite
def test_tc17_dominio_vuoto(fixture_file, res_root):
    with pytest.raises(ValueError):
        run(str(fixture_file("f8")), theta=0, results_root=str(res_root))


def test_tc18_dominio_singolo_theta_zero(fixture_file, res_root):          # INC-01
    with pytest.raises(ZeroDivisionError):
        run(str(fixture_file("f9")), theta=0, results_root=str(res_root))


# --------------------------------------------------------------- tipi
def test_tc19_bitvector(fixture_file, res_root):
    smt = fixture_file("f5")
    run(str(smt), num_samples=3, results_root=str(res_root))
    assert count_status(read_rows(_csv(res_root, smt)), "SAT") == 3


def test_tc20_stringhe(fixture_file, res_root):
    smt = fixture_file("f6")
    run(str(smt), num_samples=2, results_root=str(res_root))
    assert count_status(read_rows(_csv(res_root, smt)), "SAT") == 2


# --------------------------------------------------------------- interruzione
def test_tc21_interruzione_da_utente(fixture_file, res_root, capsys):
    smt = fixture_file("f2")
    timer = threading.Timer(3, _thread.interrupt_main)   # equivale a SIGINT (Ctrl+C)
    timer.start()
    try:
        with pytest.raises(KeyboardInterrupt):
            run(str(smt), results_root=str(res_root))
    finally:
        timer.cancel()
    assert "KeyboardInterrupt ricevuto" in capsys.readouterr().out
    assert len(read_rows(_csv(res_root, smt))) >= 1
