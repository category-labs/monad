"""Python encoders for Monad's native consensus block format.

Mirrors the C++ decoders in:
  - category/execution/monad/core/rlp/monad_block_rlp.cpp
  - category/execution/ethereum/core/rlp/block_rlp.cpp
  - category/execution/ethereum/core/rlp/receipt_rlp.cpp

We target MonadConsensusBlockHeaderV2 because MONAD_NEXT >= MONAD_FOUR.

Only what we actually need for devnet integration tests is implemented —
empty ommers, empty withdrawals, empty delayed_execution_results, etc.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

import rlp
from eth_utils import keccak

EMPTY_LIST_RLP = b"\xc0"             # keccak of this = empty-list hash
EMPTY_LIST_HASH = keccak(EMPTY_LIST_RLP)

# Standard Ethereum MPT empty root = keccak(rlp(b"")) = keccak(0x80).
EMPTY_ROOT = keccak(rlp.encode(b""))


# --- BlockHeader (Ethereum-compatible, full form used for ommers + execution outputs)

@dataclass
class BlockHeader:
    parent_hash: bytes = b"\x00" * 32
    ommers_hash: bytes = EMPTY_LIST_HASH
    beneficiary: bytes = b"\x00" * 20
    state_root: bytes = b"\x00" * 32
    transactions_root: bytes = EMPTY_ROOT
    receipts_root: bytes = EMPTY_ROOT
    logs_bloom: bytes = b"\x00" * 256
    difficulty: int = 0
    number: int = 0
    gas_limit: int = 0
    gas_used: int = 0
    timestamp: int = 0
    extra_data: bytes = b""
    prev_randao: bytes = b"\x00" * 32
    nonce: bytes = b"\x00" * 8
    base_fee_per_gas: Optional[int] = None
    withdrawals_root: Optional[bytes] = None
    blob_gas_used: Optional[int] = None
    excess_blob_gas: Optional[int] = None
    parent_beacon_block_root: Optional[bytes] = None
    requests_hash: Optional[bytes] = None


def encode_block_header(h: BlockHeader) -> bytes:
    """Full Ethereum block-header RLP (used for ommer encoding, delayed
    execution results, etc.). Mirror of block_rlp.cpp:encode_block_header."""
    if len(h.parent_hash) != 32 or len(h.ommers_hash) != 32 or len(h.state_root) != 32:
        raise ValueError("bytes32 field wrong size")
    fields = [
        h.parent_hash,
        h.ommers_hash,
        h.beneficiary,
        h.state_root,
        h.transactions_root,
        h.receipts_root,
        h.logs_bloom,
        h.difficulty,
        h.number,
        h.gas_limit,
        h.gas_used,
        h.timestamp,
        h.extra_data,
        h.prev_randao,
        h.nonce,
    ]
    if h.base_fee_per_gas is not None:
        fields.append(h.base_fee_per_gas)
    if h.withdrawals_root is not None:
        fields.append(h.withdrawals_root)
    if h.blob_gas_used is not None:
        fields.append(h.blob_gas_used)
    if h.excess_blob_gas is not None:
        fields.append(h.excess_blob_gas)
    if h.parent_beacon_block_root is not None:
        fields.append(h.parent_beacon_block_root)
    if h.requests_hash is not None:
        fields.append(h.requests_hash)
    return rlp.encode(fields)


# --- "execution_inputs" — a reduced BlockHeader form carried in the consensus header

def encode_execution_inputs(h: BlockHeader) -> bytes:
    """Mirror of monad_block_rlp.cpp:decode_execution_inputs — a compact subset
    of the eth block header used in the consensus header's execution_inputs slot.

    Fields (in order): ommers_hash, beneficiary, transactions_root, difficulty,
    number, gas_limit, timestamp, extra_data, prev_randao, nonce, base_fee_per_gas,
    withdrawals_root, blob_gas_used, excess_blob_gas, parent_beacon_block_root,
    requests_hash (optional)."""
    fields = [
        h.ommers_hash,
        h.beneficiary,
        h.transactions_root,
        h.difficulty,
        h.number,
        h.gas_limit,
        h.timestamp,
        h.extra_data,
        h.prev_randao,
        h.nonce,
        h.base_fee_per_gas if h.base_fee_per_gas is not None else 0,
        h.withdrawals_root if h.withdrawals_root is not None else EMPTY_ROOT,
        h.blob_gas_used if h.blob_gas_used is not None else 0,
        h.excess_blob_gas if h.excess_blob_gas is not None else 0,
        h.parent_beacon_block_root if h.parent_beacon_block_root is not None else b"\x00" * 32,
    ]
    if h.requests_hash is not None:
        fields.append(h.requests_hash)
    return rlp.encode(fields)


# --- Quorum Certificate (V1 vote used by V1/V2 consensus headers)

@dataclass
class VoteV1:
    id: bytes = b"\x00" * 32    # block_id of the block being voted on
    round: int = 0
    epoch: int = 0


@dataclass
class SignerMap:
    num_bits: int = 0
    bitmap: bytes = b""


@dataclass
class Signatures:
    signer_map: SignerMap = field(default_factory=SignerMap)
    aggregate_signature: bytes = b"\x00" * 96


@dataclass
class QuorumCertificateV1:
    vote: VoteV1 = field(default_factory=VoteV1)
    signatures: Signatures = field(default_factory=Signatures)


def encode_quorum_certificate_v1(qc: QuorumCertificateV1) -> bytes:
    vote_rlp = rlp.encode([qc.vote.id, qc.vote.round, qc.vote.epoch])
    sig_inner = rlp.encode([qc.signatures.signer_map.num_bits,
                            qc.signatures.signer_map.bitmap])
    sig_rlp = rlp.encode([sig_inner, qc.signatures.aggregate_signature],
                         infer_serializer=False)
    # Actually the signatures structure is rlp([signer_map, aggregate_signature])
    # where signer_map is itself rlp([num_bits, bitmap]).
    # We want: qc = rlp([vote, signatures]) where `signatures` is already an rlp list.
    # Build it manually to avoid py-rlp treating rlp-bytes as another item.
    return _manual_qc_rlp(qc)


def _manual_qc_rlp(qc: QuorumCertificateV1) -> bytes:
    """Hand-roll the QC RLP to match the C++ decoder's expected nesting:
      qc  = rlp_list( vote_list, signatures_list )
      vote_list    = rlp_list( id, round, epoch )
      signatures_list = rlp_list( signer_map_list, aggregate_signature_bytes )
      signer_map_list = rlp_list( num_bits, bitmap )
    """
    vote_payload = (
        rlp.encode(qc.vote.id) + rlp.encode(qc.vote.round) + rlp.encode(qc.vote.epoch)
    )
    vote = _as_list(vote_payload)

    signer_map_payload = (
        rlp.encode(qc.signatures.signer_map.num_bits)
        + rlp.encode(qc.signatures.signer_map.bitmap)
    )
    signer_map = _as_list(signer_map_payload)

    signatures_payload = signer_map + rlp.encode(qc.signatures.aggregate_signature)
    signatures = _as_list(signatures_payload)

    qc_payload = vote + signatures
    return _as_list(qc_payload)


def _as_list(payload: bytes) -> bytes:
    n = len(payload)
    if n < 56:
        return bytes([0xC0 + n]) + payload
    length_bytes = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0xF7 + len(length_bytes)]) + length_bytes + payload


# --- Monad consensus block header V2

@dataclass
class ConsensusHeaderV2:
    block_round: int = 0
    epoch: int = 0
    qc: QuorumCertificateV1 = field(default_factory=QuorumCertificateV1)
    author: bytes = b"\x00" * 33
    seqno: int = 0
    timestamp_ns: int = 0
    round_signature: bytes = b"\x00" * 96
    delayed_execution_results: list[BlockHeader] = field(default_factory=list)
    execution_inputs: BlockHeader = field(default_factory=BlockHeader)
    block_body_id: bytes = b"\x00" * 32
    base_fee: int = 0
    base_fee_trend: int = 0
    base_fee_moment: int = 0


def encode_consensus_header_v2(h: ConsensusHeaderV2) -> bytes:
    # delayed_execution_results: a list of BlockHeader each encoded as full eth header
    delayed_payload = b"".join(encode_block_header(x) for x in h.delayed_execution_results)
    delayed = _as_list(delayed_payload)

    payload = (
        rlp.encode(h.block_round)
        + rlp.encode(h.epoch)
        + _manual_qc_rlp(h.qc)
        + rlp.encode(h.author)
        + rlp.encode(h.seqno)
        + rlp.encode(h.timestamp_ns)
        + rlp.encode(h.round_signature)
        + delayed
        + encode_execution_inputs(h.execution_inputs)
        + rlp.encode(h.block_body_id)
        + rlp.encode(h.base_fee)
        + rlp.encode(h.base_fee_trend)
        + rlp.encode(h.base_fee_moment)
    )
    return _as_list(payload)


# --- Block body: rlp([ rlp([txs, ommers, withdrawals]) ])

def encode_transaction_list(tx_bytes_list: list[bytes]) -> bytes:
    # Transactions list: each tx is either direct-list (legacy, first byte >= 0xc0)
    # or a string RLP (typed 0x02, etc.). Domain txs are standard typed txs
    # whose chain_id carries the domain, so wrap typed txs in a string.
    txs_payload = b""
    for tx in tx_bytes_list:
        if tx and tx[0] >= 0xC0:
            txs_payload += tx
        else:
            txs_payload += rlp.encode(tx)
    return _as_list(txs_payload)


def encode_consensus_block_body(
    tx_bytes_list: list[bytes],
    ommers: list[BlockHeader] | None = None,
    withdrawals: list | None = None,
) -> bytes:
    ommers = ommers or []
    withdrawals = withdrawals or []

    txs_rlp = encode_transaction_list(tx_bytes_list)

    ommers_payload = b"".join(encode_block_header(o) for o in ommers)
    ommers_rlp = _as_list(ommers_payload)

    # Withdrawals: list of rlp([index, validator_index, address, amount]).
    withdrawals_payload = b""
    for w in withdrawals:
        withdrawals_payload += rlp.encode([w["index"], w["validator_index"],
                                            w["address"], w["amount"]])
    withdrawals_rlp = _as_list(withdrawals_payload)

    inner_list = _as_list(txs_rlp + ommers_rlp + withdrawals_rlp)
    return _as_list(inner_list)
