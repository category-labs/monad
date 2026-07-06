#!/usr/bin/env python3
"""Independent Ethereum-MPT helpers for Monad domain state dumps.

Root state and each domain state are ordinary Ethereum account tries:

    state trie:   keccak(address) -> rlp([nonce, balance, storage_root, code_hash])
    storage trie: keccak(slot)    -> rlp(value_without_leading_zeroes)

Private domain account tries live in the Monad DB under
DOMAIN_STATE_NIBBLE + be64(domain_id). Their roots are persisted as
domain trie metadata and are not copied into root EVM state.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from eth_utils import keccak
import rlp
from trie import HexaryTrie


NULL_HASH = keccak(b"")
EMPTY_ROOT = keccak(rlp.encode(b""))

def eth_encode_account(
    nonce: int, balance: int, storage_root: bytes, code_hash: bytes
) -> bytes:
    """Ethereum-standard account RLP."""
    return rlp.encode([nonce, balance, storage_root, code_hash])


def compute_storage_root(storage: dict[bytes, bytes]) -> bytes:
    """Compute an Ethereum storage trie root from raw 32-byte slots/values."""
    trie = HexaryTrie(db={})
    for slot, value in storage.items():
        if len(slot) != 32:
            raise ValueError(f"storage slot must be 32 bytes, got {len(slot)}")
        if len(value) != 32:
            raise ValueError(f"storage value must be 32 bytes, got {len(value)}")
        if value == b"\x00" * 32:
            continue
        trie[keccak(slot)] = rlp.encode(value.lstrip(b"\x00"))
    return trie.root_hash


@dataclass
class AccountState:
    """Ethereum-standard account with optional contract storage."""

    nonce: int = 0
    balance: int = 0
    code_hash: bytes = NULL_HASH
    storage: dict[bytes, bytes] = field(default_factory=dict)

    @property
    def storage_root(self) -> bytes:
        return compute_storage_root(self.storage)

    def encode(self) -> bytes:
        return eth_encode_account(
            self.nonce, self.balance, self.storage_root, self.code_hash
        )


def compute_state_root(accounts: dict[bytes, AccountState]) -> bytes:
    """Compute a standard Ethereum account trie root."""
    trie = HexaryTrie(db={})
    for addr, acct in accounts.items():
        if len(addr) != 20:
            raise ValueError(f"account address must be 20 bytes, got {len(addr)}")
        trie[keccak(addr)] = acct.encode()
    return trie.root_hash


def compute_sub_state_root(encoded_accounts: dict[bytes, bytes]) -> bytes:
    """Compatibility helper for callers that already encoded account leaves."""
    trie = HexaryTrie(db={})
    for addr, encoded_account in encoded_accounts.items():
        if len(addr) != 20:
            raise ValueError(f"account address must be 20 bytes, got {len(addr)}")
        trie[keccak(addr)] = encoded_account
    return trie.root_hash


def _check(name: str, condition: bool) -> bool:
    status = "OK" if condition else "MISMATCH"
    print(f"[{status}] {name}")
    return condition


def self_check() -> bool:
    zero_slot = b"\x00" * 32
    storage_with_zero = {zero_slot: zero_slot}
    storage_with_one = {zero_slot: (1).to_bytes(32, "big")}
    return all(
        [
            _check("empty account trie", compute_state_root({}) == EMPTY_ROOT),
            _check("empty storage trie", compute_storage_root({}) == EMPTY_ROOT),
            _check(
                "zero storage omitted",
                compute_storage_root(storage_with_zero) == EMPTY_ROOT,
            ),
            _check(
                "nonzero storage committed",
                compute_storage_root(storage_with_one) != EMPTY_ROOT,
            ),
        ]
    )


if __name__ == "__main__":
    raise SystemExit(0 if self_check() else 1)
