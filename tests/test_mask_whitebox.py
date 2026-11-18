"""Test white box TM-02 (TC-22..TC-27) e TM-03 (TC-28..TC-30).

TM-02: create_mask_with_coverage (solver_utils.py) - copertura dei rami DM1..DM8.
TM-03: _create_mask_for_type (solver_utils_typed.py) - ramo DT1.
Misura dei rami (opzionale): coverage run --branch -m pytest tests/test_mask_whitebox.py
"""
from unittest import mock

import pytest

import solver_utils as su
import solver_utils_typed as st
from helpers import mask_properties, seed_all


def _mask(args, seed=1):
    seed_all(seed)
    return su.create_mask_with_coverage(*args)


# --------------------------------------------------------------------------- TM-02
def test_tc22_min_maggiore_di_max_solleva_valueerror():          # DM1 si'
    with pytest.raises(ValueError):
        su.create_mask_with_coverage(10, 5, 50, 0.25)


def test_tc23_dominio_piccolo_band_width_1():                     # DM2 si', DM8 no
    mask = _mask((0, 99, 30, 0.005))
    props, cov = mask_properties(mask, 0, 99, 30)
    assert all(props.values()), (props, cov)
    assert len(mask) == 20


def test_tc24_dominio_medio_band_width_maggiore_di_1():           # DM2 no
    mask = _mask((0, 999, 30, 0.005))
    props, cov = mask_properties(mask, 0, 999, 30)
    assert all(props.values()), (props, cov)
    assert len(mask) == 48


def test_tc25_copertura_sopra_il_target_decrementa_intervalli():  # DM7 si'
    mask = _mask((0, 9999, 50, 0.05))
    props, cov = mask_properties(mask, 0, 9999, 50)
    assert all(props.values()), (props, cov)
    assert len(mask) == 10


def test_tc26_dominio_con_estremi_negativi():
    mask = _mask((-100, 100, 40, 0.01))
    props, cov = mask_properties(mask, -100, 100, 40)
    assert all(props.values()), (props, cov)
    assert len(mask) == 28


def test_tc27_dominio_di_un_solo_valore_zerodivisionerror():      # INC-01
    with pytest.raises(ZeroDivisionError):
        su.create_mask_with_coverage(5, 5, 30, 0.005)


# --------------------------------------------------------------------------- TM-03
def _typed_mask(var_type, lb, ub, cov, delta, seed=5):
    seed_all(seed)
    return st._create_mask_for_type(var_type, lb, ub, cov, delta)


def test_tc28_int_ramo_diretto():                                  # DT1 no
    seed_all(5)
    expected = su.create_mask_with_coverage(0, 999, 50, 0.005)
    with mock.patch.object(st, "_create_string_interval_mask",
                           wraps=st._create_string_interval_mask) as spy:
        got = _typed_mask("Int", 0, 999, 50, 0.005)
    assert got == expected
    spy.assert_not_called()
    assert len(got) == 67


def test_tc29_string_passa_da_create_string_interval_mask():       # DT1 si'
    seed_all(5)
    expected = su.create_mask_with_coverage(0, 999, 50, 0.005)
    with mock.patch.object(st, "_create_string_interval_mask",
                           wraps=st._create_string_interval_mask) as spy:
        got = _typed_mask("String", 0, 999, 50, 0.005)
    assert got == expected
    spy.assert_called_once()
    assert len(got) == 67


def test_tc30_bitvec_ramo_diretto():                               # DT1 no
    seed_all(5)
    expected = su.create_mask_with_coverage(0, 255, 50, 0.01)
    with mock.patch.object(st, "_create_string_interval_mask",
                           wraps=st._create_string_interval_mask) as spy:
        got = _typed_mask("(_ BitVec 8)", 0, 255, 50, 0.01)
    assert got == expected
    spy.assert_not_called()
    assert len(got) == 38
