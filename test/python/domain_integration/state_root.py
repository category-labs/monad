"""State-root validation for monad-cli full-state JSON dumps."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

from eth_utils import keccak
import rlp
from trie import HexaryTrie

def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path}")
    mod = importlib.util.module_from_spec(spec)
    # dataclasses' InitVar resolution uses sys.modules[cls.__module__]; we
    # register every loaded helper before exec_module so decorators can find
    # the module namespace.
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def _load_state_root_helpers():
    repo_root = Path(__file__).resolve().parents[3]
    path = repo_root / "scripts" / "compute_domain_state_root.py"
    return _load_module("_monad_state_root", path)


def _load_page_commit_helpers():
    repo_root = Path(__file__).resolve().parents[3]
    path = repo_root / "scripts" / "page_commit_reference.py"
    return _load_module("_monad_page_commit", path)


_mod = _load_state_root_helpers()
_page_mod = _load_page_commit_helpers()

AccountState = _mod.AccountState
eth_encode_account = _mod.eth_encode_account
compute_state_root = _mod.compute_state_root
compute_sub_state_root = _mod.compute_sub_state_root
compute_storage_root = _mod.compute_storage_root
NULL_HASH = _mod.NULL_HASH
EMPTY_ROOT = _mod.EMPTY_ROOT

page_commit = _page_mod.page_commit
PAGE_SLOTS = _page_mod.PAGE_SLOTS
SLOT_SIZE = _page_mod.SLOT_SIZE
PAGE_SIZE = _page_mod.PAGE_SIZE
PAGE_KEY_SHIFT = PAGE_SLOTS.bit_length() - 1
SLOT_OFFSET_MASK = PAGE_SLOTS - 1

assert PAGE_SLOTS == 1 << PAGE_KEY_SHIFT


def _parse_addr(s: str) -> bytes:
    assert s.startswith("0x") and len(s) == 42, s
    return bytes.fromhex(s[2:])


def _parse_bytes32(s: str) -> bytes:
    assert s.startswith("0x") and len(s) == 66, s
    return bytes.fromhex(s[2:])


def _parse_domain_key(s: str) -> int:
    assert s.startswith("0x") and len(s) == 18, s
    return int(s[2:], 16)


def _parse_account(info: dict) -> AccountState:
    storage: dict[bytes, bytes] = {}
    for slot_hex, val_hex in info.get("storage", {}).items():
        storage[_parse_bytes32(slot_hex)] = _parse_bytes32(val_hex)

    return AccountState(
        balance=int(info["balance"]),
        nonce=int(info["nonce"]),
        code_hash=_parse_bytes32(info["code_hash"]),
        storage=storage,
    )


def _dump_accounts_to_state(accounts_json: dict) -> dict[bytes, AccountState]:
    accounts: dict[bytes, AccountState] = {}
    for addr_hex, info in accounts_json.items():
        if info is None:
            continue
        accounts[_parse_addr(addr_hex)] = _parse_account(info)
    return accounts


def dump_to_accounts(dump: dict) -> dict[bytes, AccountState]:
    """Convert root dump accounts into compute_state_root input form."""
    return _dump_accounts_to_state(dump["accounts"])


def dump_to_domains(dump: dict) -> dict[int, dict[bytes, AccountState]]:
    """Convert domain dump accounts into per-domain account maps."""
    domains: dict[int, dict[bytes, AccountState]] = {}
    for domain_hex, domain_info in dump.get("domains", {}).items():
        domains[_parse_domain_key(domain_hex)] = _dump_accounts_to_state(
            domain_info.get("accounts", {})
        )
    return domains


def _assert_root(label: str, computed: bytes, expected: bytes) -> None:
    if computed != expected:
        raise AssertionError(
            f"{label} root mismatch.\n"
            f"  computed: 0x{computed.hex()}\n"
            f"  binary:   0x{expected.hex()}"
        )


def _page_key_and_offset(slot: bytes) -> tuple[bytes, int]:
    slot_int = int.from_bytes(slot, "big")
    page_key = (slot_int >> PAGE_KEY_SHIFT).to_bytes(32, "big")
    return page_key, slot_int & SLOT_OFFSET_MASK


def compute_page_storage_root(storage: dict[bytes, bytes]) -> bytes:
    """Compute a Monad page-encoded storage trie root from raw slots/values."""
    pages: dict[bytes, dict[int, bytes]] = {}
    for slot, value in storage.items():
        if len(slot) != 32:
            raise ValueError(f"storage slot must be 32 bytes, got {len(slot)}")
        if len(value) != 32:
            raise ValueError(f"storage value must be 32 bytes, got {len(value)}")
        if value == b"\x00" * 32:
            continue
        page_key, offset = _page_key_and_offset(slot)
        pages.setdefault(page_key, {})[offset] = value

    trie = HexaryTrie(db={})
    for page_key, slots in pages.items():
        page = bytearray(PAGE_SIZE)
        for offset, value in slots.items():
            start = offset * SLOT_SIZE
            page[start:start + SLOT_SIZE] = value
        trie[keccak(page_key)] = rlp.encode(page_commit(bytes(page)))
    return trie.root_hash


def compute_page_state_root(accounts: dict[bytes, AccountState]) -> bytes:
    """Compute an account trie root with Monad page-encoded storage roots."""
    trie = HexaryTrie(db={})
    for addr, acct in accounts.items():
        if len(addr) != 20:
            raise ValueError(f"account address must be 20 bytes, got {len(addr)}")
        storage_root = compute_page_storage_root(acct.storage)
        trie[keccak(addr)] = eth_encode_account(
            acct.nonce, acct.balance, storage_root, acct.code_hash
        )
    return trie.root_hash


def validate_state_root(dump: dict) -> None:
    """Recompute root and private domain state roots from the dump."""
    root_accounts = dump_to_accounts(dump)
    page_encoded = dump.get("storage_encoding") == "page"
    state_root_fn = compute_page_state_root if page_encoded else compute_state_root

    root_computed = state_root_fn(root_accounts)
    _assert_root("root state", root_computed, _parse_bytes32(dump["state_root"]))

    domain_dumps = dump.get("domains", {})
    for domain_hex, domain_info in domain_dumps.items():
        _parse_domain_key(domain_hex)
        domain_accounts = _dump_accounts_to_state(domain_info.get("accounts", {}))
        domain_computed = state_root_fn(domain_accounts)
        domain_root = _parse_bytes32(domain_info["state_root"])
        _assert_root(f"domain {domain_hex}", domain_computed, domain_root)


__all__ = [
    "AccountState",
    "compute_state_root",
    "compute_page_state_root",
    "compute_page_storage_root",
    "compute_sub_state_root",
    "compute_storage_root",
    "NULL_HASH",
    "EMPTY_ROOT",
    "dump_to_accounts",
    "dump_to_domains",
    "validate_state_root",
]
