"""Subprocess wrappers for the monad binary and monad-cli."""

from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping, Optional

REPO_ROOT = Path(__file__).resolve().parents[3]
MONAD_BINARY = REPO_ROOT / "build" / "cmd" / "monad"
MONAD_CLI_BINARY = REPO_ROOT / "build" / "cmd" / "monad-cli"
MONAD_MPT_BINARY = REPO_ROOT / "build" / "category" / "mpt" / "monad-mpt"


def create_triedb(storage: Path, size_bytes: int = 16 * 1024 * 1024 * 1024) -> None:
    """Initialize a triedb at `storage`.

    If `storage` is an existing block device (e.g. `/dev/triedb`), we
    `blkdiscard` it to clear any prior state. Otherwise we create a file of
    `size_bytes` (default 16 GiB — page storage needs larger root-offset
    chunks).
    """
    storage.parent.mkdir(parents=True, exist_ok=True)
    if storage.exists() and storage.is_block_device():
        subprocess.run(
            ["sudo", "-n", "blkdiscard", str(storage)],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    else:
        with open(storage, "wb") as f:
            f.truncate(size_bytes)
    subprocess.run(
        [
            str(MONAD_MPT_BINARY),
            "--storage",
            str(storage),
            "--create",
            "--state-machine",
            "monad",
            "--chunk-capacity",
            "29",
            "--root-offsets-chunk-count",
            "2",
            "--yes",
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )


@dataclass
class MonadResult:
    returncode: int
    stdout: str
    stderr: str


def run_monad(
    ledger_dir: Path,
    triedb: Path,
    nblocks: int,
    *,
    timeout: float = 120.0,
    private_domain_keys: Mapping[int, Path] | None = None,
    private_domain_spokes: Mapping[int, bytes] | None = None,
    private_domain_sequencer: bytes | None = None,
) -> MonadResult:
    """Run the monad binary in native (non --as-eth-blocks) mode."""
    cmd = [
        str(MONAD_BINARY),
        "--chain",
        "monad_devnet",
        "--block-db",
        str(ledger_dir),
        "--db",
        str(triedb),
        "--nblocks",
        str(nblocks),
    ]
    if private_domain_keys is not None:
        if private_domain_spokes is None or (
            private_domain_keys.keys() != private_domain_spokes.keys()
        ):
            raise ValueError(
                "private domain keys and spoke mappings must have identical IDs"
            )
        for domain_id, path in private_domain_keys.items():
            spoke = private_domain_spokes[domain_id]
            if len(spoke) != 20 or spoke == bytes(20):
                raise ValueError(
                    "private domain spoke must be a nonzero 20-byte address"
                )
            cmd.extend(
                [
                    "--private-domain",
                    str(domain_id),
                    spoke.hex(),
                    str(path),
                ]
            )
    if private_domain_sequencer is not None:
        if len(private_domain_sequencer) != 20:
            raise ValueError("private domain sequencer must be 20 bytes")
        cmd.extend(
            [
                "--private-domain-sequencer",
                private_domain_sequencer.hex(),
            ]
        )
    env = os.environ.copy()
    env.setdefault("LD_BIND_NOW", "1")
    p = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=timeout)
    return MonadResult(p.returncode, p.stdout, p.stderr)


@dataclass
class AccountDump:
    balance: int
    nonce: int
    code_hash: bytes


@dataclass
class StateDump:
    merkle_root: bytes
    accounts: dict[bytes, Optional[AccountDump]]  # None => not present


_ACCT_RE = re.compile(
    r"Account\{balance=(\d+), code_hash=0x([0-9a-fA-F]{64}), nonce=(\d+)"
)
_ROOT_RE = re.compile(r"Merkle root is 0x([0-9a-fA-F]{64})")
_NOT_FOUND_RE = re.compile(r"Could not find account 0x", re.I)
_RECEIPT_RE = re.compile(r"Status=(\d+).*?Gas Used=(\d+)", re.S)
_RECEIPT_LOG_RE = re.compile(
    r"Log\{Data=0x([0-9a-fA-F]*) Topics=\[([^]]*)\] " r"Address=0x([0-9a-fA-F]{40})\}"
)
_TOPIC_RE = re.compile(r"0x([0-9a-fA-F]{64})")


@dataclass(frozen=True)
class ReceiptLogDump:
    data: bytes
    topics: tuple[bytes, ...]
    address: bytes


@dataclass
class ReceiptDump:
    status: int
    gas_used: int
    logs: tuple[ReceiptLogDump, ...] = ()


def _parse_receipt(output: str) -> ReceiptDump | None:
    match = _RECEIPT_RE.search(output)
    if match is None:
        return None
    logs = tuple(
        ReceiptLogDump(
            data=bytes.fromhex(log.group(1)),
            topics=tuple(
                bytes.fromhex(topic) for topic in _TOPIC_RE.findall(log.group(2))
            ),
            address=bytes.fromhex(log.group(3)),
        )
        for log in _RECEIPT_LOG_RE.finditer(output)
    )
    return ReceiptDump(
        status=int(match.group(1)),
        gas_used=int(match.group(2)),
        logs=logs,
    )


def query_receipts(triedb: Path, version: int, count: int) -> list[ReceiptDump]:
    """Read receipt[0..count-1] for `version` from the triedb via monad-cli."""
    import pexpect

    p = pexpect.spawn(
        str(MONAD_CLI_BINARY),
        ["--db", str(triedb), "--it"],
        encoding="utf-8",
        timeout=60,
    )
    out: list[ReceiptDump] = []
    try:
        p.expect_exact("(monaddb)")
        p.sendline(f"version {version}")
        p.expect_exact("(monaddb)")
        p.sendline("finalized")
        p.expect_exact("(monaddb)")
        p.sendline("table receipt")
        p.expect_exact("(monaddb)")
        for i in range(count):
            p.sendline(f"get {i}")
            p.expect_exact("(monaddb)")
            receipt = _parse_receipt(p.before)
            if receipt is None:
                raise RuntimeError(f"could not parse receipt {i} from:\n{p.before}")
            out.append(receipt)
        p.sendline("exit")
        p.expect(pexpect.EOF)
    finally:
        if p.isalive():
            p.close(force=True)
    return out


def query_domain_receipt(
    triedb: Path, version: int, domain_id: int, index: int
) -> ReceiptDump | None:
    """Read a private-domain receipt, or return None when absent."""
    import pexpect

    p = pexpect.spawn(
        str(MONAD_CLI_BINARY),
        ["--db", str(triedb), "--it"],
        encoding="utf-8",
        timeout=60,
    )
    try:
        p.expect_exact("(monaddb)")
        p.sendline(f"version {version}")
        p.expect_exact("(monaddb)")
        p.sendline("finalized")
        p.expect_exact("(monaddb)")
        p.sendline("table domain_receipt")
        p.expect_exact("(monaddb)")
        p.sendline(f"get {domain_id}:{index}")
        p.expect_exact("(monaddb)")
        if "Could not find domain receipt" in p.before:
            return None
        receipt = _parse_receipt(p.before)
        if receipt is None:
            raise RuntimeError(f"could not parse domain receipt:\n{p.before}")
        return receipt
    finally:
        if p.isalive():
            p.close(force=True)


_SENDER_RE = re.compile(r"Sender=0x([0-9a-fA-F]{40})")
_ENCODED_TRANSACTION_RE = re.compile(r"Encoded=0x([0-9a-fA-F]+)")


@dataclass
class DomainTransactionDump:
    encoded: bytes
    sender: bytes


def query_domain_transaction(
    triedb: Path, version: int, domain_id: int, index: int
) -> DomainTransactionDump | None:
    """Read a stored domain transaction and sender field."""
    import pexpect

    p = pexpect.spawn(
        str(MONAD_CLI_BINARY),
        ["--db", str(triedb), "--it"],
        encoding="utf-8",
        timeout=60,
    )
    try:
        p.expect_exact("(monaddb)")
        p.sendline(f"version {version}")
        p.expect_exact("(monaddb)")
        p.sendline("finalized")
        p.expect_exact("(monaddb)")
        p.sendline("table domain_transaction")
        p.expect_exact("(monaddb)")
        p.sendline(f"get {domain_id}:{index}")
        p.expect_exact("(monaddb)")
        if "Could not find domain transaction" in p.before:
            return None
        sender = _SENDER_RE.search(p.before)
        encoded = _ENCODED_TRANSACTION_RE.search(p.before)
        if not encoded or not sender:
            raise RuntimeError(f"could not parse domain transaction:\n{p.before}")
        return DomainTransactionDump(
            encoded=bytes.fromhex(encoded.group(1)),
            sender=bytes.fromhex(sender.group(1)),
        )
    finally:
        if p.isalive():
            p.close(force=True)


def query_domain_transaction_sender(
    triedb: Path, version: int, domain_id: int, index: int
) -> bytes | None:
    """Read the sender field, including the zero-address failure placeholder."""
    transaction = query_domain_transaction(triedb, version, domain_id, index)
    return None if transaction is None else transaction.sender


_DOMAIN_TRANSACTION_LOCATION_RE = re.compile(r"Block=(\d+) Index=(\d+)")


def query_domain_transaction_location(
    triedb: Path, version: int, domain_id: int, transaction_hash: bytes
) -> tuple[int, int] | None:
    """Resolve a domain transaction hash to its block and local index."""
    if len(transaction_hash) != 32:
        raise ValueError("transaction hash must be 32 bytes")
    import pexpect

    p = pexpect.spawn(
        str(MONAD_CLI_BINARY),
        ["--db", str(triedb), "--it"],
        encoding="utf-8",
        timeout=60,
    )
    try:
        p.expect_exact("(monaddb)")
        p.sendline(f"version {version}")
        p.expect_exact("(monaddb)")
        p.sendline("finalized")
        p.expect_exact("(monaddb)")
        p.sendline("table domain_transaction_hash")
        p.expect_exact("(monaddb)")
        p.sendline(f"get {domain_id}:0x{transaction_hash.hex()}")
        p.expect_exact("(monaddb)")
        if "Could not find domain transaction hash" in p.before:
            return None
        location = _DOMAIN_TRANSACTION_LOCATION_RE.search(p.before)
        if not location:
            raise RuntimeError(
                f"could not parse domain transaction location:\n{p.before}"
            )
        return int(location.group(1)), int(location.group(2))
    finally:
        if p.isalive():
            p.close(force=True)


def query_domain_transaction_and_receipt_by_hash(
    triedb: Path, version: int, domain_id: int, transaction_hash: bytes
) -> tuple[DomainTransactionDump, ReceiptDump] | None:
    """Resolve a hash and read its historical transaction and receipt."""
    location = query_domain_transaction_location(
        triedb, version, domain_id, transaction_hash
    )
    if location is None:
        return None
    block_number, index = location
    transaction = query_domain_transaction(triedb, block_number, domain_id, index)
    receipt = query_domain_receipt(triedb, block_number, domain_id, index)
    if transaction is None or receipt is None:
        raise RuntimeError(
            "domain transaction hash points to missing transaction/receipt"
        )
    return transaction, receipt


def query_state(
    triedb: Path,
    version: int,
    addresses: list[bytes],
) -> StateDump:
    """Open the triedb via monad-cli --it, record the state merkle root, and
    read out each address's account. Returns a StateDump.

    Caveat: monad-cli's interactive mode queries root-trie accounts only.
    Private domain roots remain in their domain tries and are inspected
    through the domain-aware query helpers or ``--dump-state``."""
    import pexpect

    p = pexpect.spawn(
        str(MONAD_CLI_BINARY),
        ["--db", str(triedb), "--it"],
        encoding="utf-8",
        timeout=60,
    )
    try:
        p.expect_exact("(monaddb)")
        p.sendline(f"version {version}")
        p.expect_exact("(monaddb)")
        p.sendline("finalized")
        p.expect_exact("(monaddb)")
        p.sendline("table state")
        p.expect_exact("(monaddb)")
        # The merkle-root line was printed before the prompt we just matched.
        root_match = _ROOT_RE.search(p.before)
        if not root_match:
            raise RuntimeError(f"could not find merkle root in:\n{p.before}")
        merkle_root = bytes.fromhex(root_match.group(1))

        accounts: dict[bytes, Optional[AccountDump]] = {}
        for addr in addresses:
            p.sendline(f"get 0x{addr.hex()}")
            p.expect_exact("(monaddb)")
            if _NOT_FOUND_RE.search(p.before):
                accounts[addr] = None
                continue
            m = _ACCT_RE.search(p.before)
            if not m:
                raise RuntimeError(
                    f"could not parse account {addr.hex()} from:\n{p.before}"
                )
            accounts[addr] = AccountDump(
                balance=int(m.group(1)),
                code_hash=bytes.fromhex(m.group(2)),
                nonce=int(m.group(3)),
            )

        p.sendline("exit")
        p.expect(pexpect.EOF)
        return StateDump(merkle_root=merkle_root, accounts=accounts)
    finally:
        if p.isalive():
            p.close(force=True)
