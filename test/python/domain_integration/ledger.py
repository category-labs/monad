"""Filesystem layout for a native Monad consensus ledger.

Layout (from cmd/monad/runloop_monad.cpp and cmd/monad/file_io.cpp):

  <ledger_dir>/
    headers/
      <block_id_hex>        # RLP-encoded consensus header; filename = blake3(contents)
      proposed_head         # symlink to the most recent proposed block's header file
      finalized_head        # symlink to the most recent finalized block's header file
    bodies/
      <body_id_hex>         # RLP-encoded consensus body; filename = blake3(contents)

The binary verifies filename-as-checksum on every read (file_io.cpp:41).
`head_pointer_to_id` reads the symlink target's stem (the hex filename).
"""

from __future__ import annotations

import os
from pathlib import Path

import blake3 as blake3_mod


def blake3(data: bytes) -> bytes:
    return blake3_mod.blake3(data).digest()


def write_header(ledger_dir: Path, header_rlp: bytes) -> bytes:
    """Write header_rlp to headers/<blake3_hex>; return the 32-byte block_id."""
    block_id = blake3(header_rlp)
    path = ledger_dir / "headers" / block_id.hex()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(header_rlp)
    return block_id


def write_body(ledger_dir: Path, body_rlp: bytes) -> bytes:
    """Write body_rlp to bodies/<blake3_hex>; return the 32-byte body_id."""
    body_id = blake3(body_rlp)
    path = ledger_dir / "bodies" / body_id.hex()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(body_rlp)
    return body_id


def set_head(ledger_dir: Path, head_name: str, block_id: bytes) -> None:
    """Create or replace a headers/<head_name> symlink pointing at the block file."""
    link = ledger_dir / "headers" / head_name
    target = Path(block_id.hex())   # relative link, resolves inside headers/
    if link.exists() or link.is_symlink():
        link.unlink()
    os.symlink(target, link)
