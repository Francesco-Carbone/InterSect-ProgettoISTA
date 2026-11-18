import pytest

from helpers import write_fixture


@pytest.fixture
def smt_dir(tmp_path):
    """Cartella temporanea dei file SMT (nome fisso: serve al nome della cartella risultati)."""
    return tmp_path / "smt"


@pytest.fixture
def res_root(tmp_path):
    """Cartella temporanea passata a intervalGuidedSampler come results_root."""
    return tmp_path / "res"


@pytest.fixture
def fixture_file(smt_dir):
    """Factory: fixture_file("f1") scrive F1 e ne restituisce il percorso."""
    def _make(name):
        return write_fixture(smt_dir, name)
    return _make
