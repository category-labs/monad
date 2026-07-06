"""Calldata builder for the external domain sequencing contract."""

from __future__ import annotations

from .constants import SELECTOR_SEQUENCE_TO_DOMAIN


def _abi_uint256(v: int) -> bytes:
    if v < 0 or v >> 256 != 0:
        raise ValueError("uint256 out of range")
    return v.to_bytes(32, "big")


def _abi_uint64(v: int) -> bytes:
    if v < 0 or v >> 64 != 0:
        raise ValueError("uint64 out of range")
    return _abi_uint256(v)


def sequence_to_domain_calldata(domain_chain_id: int, payload: bytes) -> bytes:
    """Canonical ABI encoding of sequenceToDomain(uint64,bytes)."""
    padding = (-len(payload)) % 32
    return (
        SELECTOR_SEQUENCE_TO_DOMAIN
        + _abi_uint64(domain_chain_id)
        + _abi_uint256(64)
        + _abi_uint256(len(payload))
        + payload
        + b"\x00" * padding
    )
