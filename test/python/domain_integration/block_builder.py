"""High-level: assemble signed consensus blocks from a scenario spec and
write them to an on-disk Monad consensus ledger.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import rlp
from trie import HexaryTrie

from .consensus import (
    BlockHeader,
    ConsensusHeaderV2,
    EMPTY_LIST_HASH,
    EMPTY_ROOT,
    QuorumCertificateV1,
    VoteV1,
    encode_consensus_block_body,
    encode_consensus_header_v2,
)
from .ledger import blake3, set_head, write_body, write_header
from .tx import Tx, sign_tx


@dataclass
class BlockSpec:
    """One block in a scenario."""

    seqno: int
    txs: list[tuple[Tx, bytes]]  # (tx, signer_private_key)
    timestamp: int
    gas_limit: int = 150_000_000
    base_fee_per_gas: int = 0
    beneficiary: bytes = b"\x00" * 20
    extra_data: bytes = b""
    difficulty: int = 0


def transactions_root(tx_bytes_list: list[bytes]) -> bytes:
    """MPT of {rlp(index) -> tx_bytes[i]}."""
    t = HexaryTrie(db={})
    for i, tx in enumerate(tx_bytes_list):
        t[rlp.encode(i)] = tx
    return t.root_hash


def build_ledger(ledger_dir: Path, blocks: list[BlockSpec]) -> list[bytes]:
    """Write the blocks to ledger_dir; return list of block_ids."""
    ledger_dir.mkdir(parents=True, exist_ok=True)
    (ledger_dir / "headers").mkdir(exist_ok=True)
    (ledger_dir / "bodies").mkdir(exist_ok=True)

    prev_block_id = b"\x00" * 32  # genesis anchor
    block_ids: list[bytes] = []

    for i, spec in enumerate(blocks):
        # 1) Sign each direct tx. `sign_tx` returns the standard EIP-1559 bytes
        # — the domain is carried in tx.chain_id, so no envelope wrapping.
        tx_bytes_list = [sign_tx(tx, key) for tx, key in spec.txs]
        # 2) Compute transactions_root (MPT of rlp(index) -> tx bytes; same
        # as `commit_builder.cpp:214`).
        txs_root = transactions_root(tx_bytes_list)

        # 3) Build the execution-inputs BlockHeader.
        exec_inputs = BlockHeader(
            ommers_hash=EMPTY_LIST_HASH,
            beneficiary=spec.beneficiary,
            transactions_root=txs_root,
            difficulty=spec.difficulty,
            number=spec.seqno,
            gas_limit=spec.gas_limit,
            timestamp=spec.timestamp,
            extra_data=spec.extra_data,
            prev_randao=b"\x00" * 32,
            nonce=b"\x00" * 8,
            base_fee_per_gas=spec.base_fee_per_gas,
            withdrawals_root=EMPTY_ROOT,
            blob_gas_used=0,
            excess_blob_gas=0,
            parent_beacon_block_root=b"\x00" * 32,
            requests_hash=b"\x00" * 32,     # EIP-7685, required at PRAGUE+
        )

        # 4) Body: one rlp list wrapping [txs, ommers, withdrawals].
        body_rlp = encode_consensus_block_body(
            tx_bytes_list,
            ommers=[],
            withdrawals=[],
        )
        body_id = write_body(ledger_dir, body_rlp)

        # 5) Consensus header V2.
        header = ConsensusHeaderV2(
            block_round=spec.seqno,
            epoch=0,
            qc=QuorumCertificateV1(
                vote=VoteV1(id=prev_block_id, round=max(0, spec.seqno - 1), epoch=0),
            ),
            author=b"\x00" * 33,
            seqno=spec.seqno,
            timestamp_ns=spec.timestamp * 1_000_000_000,
            round_signature=b"\x00" * 96,
            delayed_execution_results=[],
            execution_inputs=exec_inputs,
            block_body_id=body_id,
            base_fee=spec.base_fee_per_gas,
            base_fee_trend=0,
            base_fee_moment=0,
        )
        header_rlp = encode_consensus_header_v2(header)
        block_id = write_header(ledger_dir, header_rlp)
        block_ids.append(block_id)
        prev_block_id = block_id

    # Finalize everything: both proposed_head and finalized_head point at the last block.
    if block_ids:
        set_head(ledger_dir, "proposed_head", block_ids[-1])
        set_head(ledger_dir, "finalized_head", block_ids[-1])

    return block_ids
