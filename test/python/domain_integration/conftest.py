"""Pytest fixtures for domain integration tests.

Each test gets a fresh MONAD_DEVNET from genesis — the fixture creates a
throwaway triedb and an empty ledger directory.
"""

from __future__ import annotations

import shutil
from dataclasses import dataclass
from pathlib import Path

import pytest

from .monad_runner import create_triedb


@dataclass
class FreshEnv:
    root: Path
    ledger: Path          # <root>/ledger — written to by build_ledger
    triedb: Path          # triedb storage file


@pytest.fixture(scope="session")
def worker_triedb_root(
    request: pytest.FixtureRequest,
    tmp_path_factory: pytest.TempPathFactory,
) -> Path:
    worker_id = getattr(request.config, "workerinput", {}).get("workerid", "master")
    root = tmp_path_factory.getbasetemp() / f"monad_domain_integration_{worker_id}"
    root.mkdir()
    yield root
    shutil.rmtree(root, ignore_errors=True)


@pytest.fixture
def fresh_env(tmp_path: Path, worker_triedb_root: Path) -> FreshEnv:
    """Fresh devnet genesis per test. Creates a brand-new ledger directory
    under pytest's per-test tmp_path, and recreates a per-worker triedb."""
    root = tmp_path / "monad"
    root.mkdir()
    ledger = root / "ledger"
    ledger.mkdir()
    (ledger / "headers").mkdir()
    (ledger / "bodies").mkdir()

    # xdist runs tests sequentially inside each worker. Reusing one triedb file
    # per worker avoids cross-worker races without retaining one 16-GiB file per
    # test for the whole pytest session.
    triedb = worker_triedb_root / "triedb.bin"
    if triedb.exists():
        triedb.unlink()
    create_triedb(triedb)

    return FreshEnv(root=root, ledger=ledger, triedb=triedb)
