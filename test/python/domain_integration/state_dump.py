"""Full-state dumper for private domain integration tests."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

from .monad_runner import MONAD_CLI_BINARY


def dump_state(triedb: Path, version: int) -> dict:
    """Run `monad-cli --dump-state` and parse the resulting JSON."""
    out_path = triedb.parent / f"monad_domain_dump_v{version}.json"
    subprocess.run(
        [
            str(MONAD_CLI_BINARY),
            "--db", str(triedb),
            "--version", str(version),
            "--dump-state", str(out_path),
        ],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.PIPE,
    )
    return json.loads(out_path.read_text())
