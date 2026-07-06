"""EIP-1559 signing for root and private gasless transactions."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from eth_account import Account
from eth_utils import keccak

from .constants import DEVNET_CHAIN_ID

TX_TYPE_EIP1559 = 0x02


@dataclass
class Tx:
    """EIP-1559 tx. `chain_id` carries the domain when it differs from
    the network chain_id (upper bytes = domain; low 2 bytes = network id)."""

    nonce: int
    gas_limit: int
    max_priority_fee_per_gas: int
    max_fee_per_gas: int
    to: Optional[bytes]          # 20 bytes or None (for CREATE)
    value: int
    data: bytes = b""
    access_list: list = field(default_factory=list)
    chain_id: int = DEVNET_CHAIN_ID


def sign_inner_tx(tx: Tx, private_key: bytes) -> bytes:
    """Sign `tx` with EIP-1559 semantics and return the RLP bytes, starting
    with the 0x02 type prefix."""
    signed = Account.sign_transaction(
        {
            "type": TX_TYPE_EIP1559,
            "chainId": tx.chain_id,
            "nonce": tx.nonce,
            "maxPriorityFeePerGas": tx.max_priority_fee_per_gas,
            "maxFeePerGas": tx.max_fee_per_gas,
            "gas": tx.gas_limit,
            "to": tx.to if tx.to is not None else b"",
            "value": tx.value,
            "data": tx.data,
            "accessList": tx.access_list,
        },
        private_key.hex(),
    )
    inner = bytes(signed.raw_transaction)
    assert inner[0] == TX_TYPE_EIP1559
    return inner


def sign_tx(tx: Tx, private_key: bytes) -> bytes:
    """Sign ``tx`` and return its serialized transaction bytes.

    A private inner transaction is a standard EIP-1559 transaction with a
    domain-qualified chain ID; its L1 envelope is built separately.
    """
    return sign_inner_tx(tx, private_key)


def domain_chain_id(domain_prefix: int) -> int:
    """Build a domain-qualified chain_id for the devnet. The domain
    prefix occupies the upper bytes; the low 2 bytes carry DEVNET_CHAIN_ID."""
    if domain_prefix == 0:
        raise ValueError("domain prefix must be non-zero")
    cid = (domain_prefix << 16) | DEVNET_CHAIN_ID
    if cid >> 64 != 0:
        raise ValueError("domain chain_id exceeds 64 bits")
    return cid


def domain_key(domain_chain_id: int) -> str:
    """JSON dump key for a domain id."""
    if domain_chain_id < 0 or domain_chain_id >> 64 != 0:
        raise ValueError("domain id must fit in uint64")
    return f"0x{domain_chain_id:016x}"


def tx_hash(tx_bytes: bytes) -> bytes:
    """keccak-256 of the serialized transaction (for tx root MPT key)."""
    return keccak(tx_bytes)
