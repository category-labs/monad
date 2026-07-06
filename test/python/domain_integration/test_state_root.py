from eth_utils import keccak
import pytest
import rlp
from trie import HexaryTrie

from .state_root import (
    AccountState,
    EMPTY_ROOT,
    NULL_HASH,
    PAGE_KEY_SHIFT,
    PAGE_SIZE,
    SLOT_SIZE,
    compute_page_storage_root,
    compute_page_state_root,
    compute_state_root,
    dump_to_domains,
    page_commit,
    validate_state_root,
)
from .tx import domain_chain_id, domain_key


def _slot_key(page_key: int, offset: int) -> bytes:
    return ((page_key << PAGE_KEY_SHIFT) | offset).to_bytes(32, "big")


def _manual_page_storage_root(
    pages: dict[int, dict[int, bytes]],
) -> bytes:
    trie = HexaryTrie(db={})
    for page_key, slots in pages.items():
        page = bytearray(PAGE_SIZE)
        for offset, value in slots.items():
            start = offset * SLOT_SIZE
            page[start:start + SLOT_SIZE] = value
        trie[keccak(page_key.to_bytes(32, "big"))] = rlp.encode(
            page_commit(bytes(page))
        )
    return trie.root_hash


def test_compute_page_storage_root_groups_far_offsets() -> None:
    pages = {
        0x1234: {
            0: (1).to_bytes(32, "big"),
            127: (2).to_bytes(32, "big"),
        },
        0x1235: {
            64: (3).to_bytes(32, "big"),
        },
    }
    storage = {
        _slot_key(page_key, offset): value
        for page_key, slots in pages.items()
        for offset, value in slots.items()
    }

    assert compute_page_storage_root(storage) == _manual_page_storage_root(pages)


@pytest.mark.parametrize("storage_encoding", ["slot", "page"])
def test_domain_dump_roots_are_validated_independently(storage_encoding: str) -> None:
    address = bytes.fromhex("11" * 20)
    domain_ids = [domain_chain_id(0x51), domain_chain_id(0x52)]
    root_fn = compute_page_state_root if storage_encoding == "page" else compute_state_root
    dump = {
        "accounts": {},
        "state_root": "0x" + EMPTY_ROOT.hex(),
        "storage_encoding": storage_encoding,
        "domains": {},
    }
    for nonce, domain_id in enumerate(domain_ids, start=1):
        account = AccountState(nonce=nonce)
        dump["domains"][domain_key(domain_id)] = {
            "accounts": {
                "0x" + address.hex(): {
                    "nonce": nonce,
                    "balance": 0,
                    "code_hash": "0x" + NULL_HASH.hex(),
                }
            },
            "state_root": "0x" + root_fn({address: account}).hex(),
        }

    domains = dump_to_domains(dump)
    assert domains[domain_ids[0]][address].nonce == 1
    assert domains[domain_ids[1]][address].nonce == 2
    validate_state_root(dump)

    dump["domains"][domain_key(domain_ids[1])]["state_root"] = "0x" + EMPTY_ROOT.hex()
    with pytest.raises(AssertionError, match=f"domain {domain_key(domain_ids[1])} root mismatch"):
        validate_state_root(dump)
