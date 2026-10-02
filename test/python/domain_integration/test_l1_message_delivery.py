"""End-to-end coverage for protocol delivery of L1 -> domain messages.

The hub records messages as `L1MessageRecorded` / `EncryptedL1MessageRecorded`
events. The client derives one system transaction per event, sent from the
reserved relayer to `DomainSpoke.relayL1Message`, and appends it to the
domain block of the same L1 block after the sequenced transactions.
"""

from __future__ import annotations

import rlp
from eth_abi import encode as abi_encode
from eth_utils import keccak

from .abi import sequence_to_domain_calldata
from .block_builder import BlockSpec, build_ledger
from .conftest import FreshEnv
from .constants import DEV_ACCOUNTS, DEVNET_CHAIN_ID
from .hpke import encrypt_inner_transaction, encrypt_l1_message
from .domain_hub_bytecode import DOMAIN_HUB_CREATION_CODE
from .monad_runner import (
    query_domain_receipt,
    query_domain_transaction,
    query_receipts,
    run_monad,
)
from .state_dump import dump_state
from .test_gasless_l1_scanning import (
    ACCESS_SPOKE,
    INNER_ADDR,
    INNER_KEY,
    DOMAIN_KEYS,
    DOMAIN_A,
    DOMAIN_B,
    OUTER_KEY,
    _contract_address,
    _init_code,
    _inner,
    _key_files,
    _with_committed_parent,
)
from .tx import Tx, domain_key, sign_tx

HUB_DEPLOYER, HUB_DEPLOYER_KEY = DEV_ACCOUNTS[2]
ALICE, ALICE_KEY = DEV_ACCOUNTS[3]
HUB = _contract_address(HUB_DEPLOYER, 0)

# DomainSpoke.SYSTEM_RELAYER, the client's fixed system transaction sender.
SYSTEM_RELAYER = bytes.fromhex("fffffffffffffffffffffffffffffffffffffffe")
SYSTEM_TRANSACTION_GAS_LIMIT = 2_500_000

# DomainSpoke storage layout (forge inspect): nextL1Nonce, failedL1Messages.
SPOKE_NEXT_L1_NONCE_SLOT = 5
SPOKE_FAILED_L1_MESSAGES_SLOT = 6

L1_MESSAGE_RELAYED_SIGNATURE = keccak(
    text="L1MessageRelayed(bytes32,uint64,address,address,uint256,bool)"
)
# Delivery callback the spoke invokes on the target:
# onDomainMessage(uint64 sourceChainId, address from, bytes data).
ON_DOMAIN_MESSAGE_SELECTOR = keccak(text="onDomainMessage(uint64,address,bytes)")[:4]

# Receiver: sstore(0, caller); sstore(calldataload(0x24) /* from */, calldatasize)
RECEIVER_RUNTIME = b"\x33\x60\x00\x55\x36\x60\x24\x35\x55\x00"
# Receiver that rejects every delivery: revert(0, 0)
REVERTING_RECEIVER_RUNTIME = b"\x60\x00\x60\x00\xfd"
# Receiver that burns its whole stipend: INVALID
GAS_EXHAUSTING_RECEIVER_RUNTIME = b"\xfe"


def _word(value: int | bytes) -> bytes:
    if isinstance(value, int):
        return value.to_bytes(32, "big")
    return value.rjust(32, b"\x00")


def _selector(signature: str) -> bytes:
    return keccak(text=signature)[:4]


def _l1_tx(
    nonce: int,
    to: bytes | None,
    data: bytes,
    key: bytes,
    gas_limit: int = 5_000_000,
    max_fee_per_gas: int = 0,
):
    return (
        Tx(
            nonce=nonce,
            gas_limit=gas_limit,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=max_fee_per_gas,
            to=to,
            value=0,
            data=data,
        ),
        key,
    )


def _inner_create(nonce: int, init_code: bytes, max_fee_per_gas: int = 0) -> bytes:
    """Signed domain creation transaction from INNER_KEY."""
    return sign_tx(
        Tx(
            nonce=nonce,
            gas_limit=1_000_000,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=max_fee_per_gas,
            to=None,
            value=0,
            data=init_code,
            chain_id=DOMAIN_A,
        ),
        INNER_KEY,
    )


def _sequence(nonce: int, domain_id: int, signed_inner: bytes, max_fee_per_gas: int = 0):
    """Sequence one signed domain transaction through the real hub."""
    encrypted = encrypt_inner_transaction(DOMAIN_KEYS[domain_id], signed_inner)
    return (
        Tx(
            nonce=nonce,
            gas_limit=1_500_000,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=max_fee_per_gas,
            to=HUB,
            value=0,
            data=sequence_to_domain_calldata(domain_id, encrypted),
        ),
        OUTER_KEY,
    )


def _deploy_hub(max_fee_per_gas: int = 0):
    return _l1_tx(0, None, DOMAIN_HUB_CREATION_CODE, HUB_DEPLOYER_KEY, max_fee_per_gas=max_fee_per_gas)


def _register_domain(nonce: int, domain_id: int, max_fee_per_gas: int = 0):
    data = _selector("registerDomain(uint64,uint8,address[],uint256)") + abi_encode(
        ["uint64", "uint8", "address[]", "uint256"],
        [domain_id, 0, [HUB_DEPLOYER], 1],
    )
    return _l1_tx(nonce, HUB, data, HUB_DEPLOYER_KEY, max_fee_per_gas=max_fee_per_gas)


def _send_l1_message(
    nonce: int, domain_id: int, to: bytes, data: bytes, key: bytes = ALICE_KEY, max_fee_per_gas: int = 0
):
    calldata = _selector("sendL1Message(uint64,address,bytes)") + abi_encode(
        ["uint64", "address", "bytes"], [domain_id, to, data]
    )
    return _l1_tx(nonce, HUB, calldata, key, max_fee_per_gas=max_fee_per_gas)


def _send_encrypted_l1_message(
    nonce: int, domain_id: int, ciphertext: bytes, key: bytes = ALICE_KEY, max_fee_per_gas: int = 0
):
    calldata = _selector("sendEncryptedL1Message(uint64,bytes)") + abi_encode(
        ["uint64", "bytes"], [domain_id, ciphertext]
    )
    return _l1_tx(nonce, HUB, calldata, key, max_fee_per_gas=max_fee_per_gas)


def _message_hash(
    sender: bytes, to: bytes, data: bytes, nonce: int, source_chain_id: int = DEVNET_CHAIN_ID
) -> bytes:
    """MessageLib.hashMessage: encodePacked(sourceChainId, from, to, keccak(data), nonce)."""
    return keccak(source_chain_id.to_bytes(8, "big") + sender + to + keccak(data) + _word(nonce))


def _relay_calldata(
    sender: bytes, to: bytes, data: bytes, nonce: int, source_chain_id: int = DEVNET_CHAIN_ID
) -> bytes:
    return _selector("relayL1Message(uint64,address,address,bytes,uint256)") + abi_encode(
        ["uint64", "address", "address", "bytes", "uint256"],
        [source_chain_id, sender, to, data, nonce],
    )


def _expected_system_transaction(
    domain_id: int,
    relayer_nonce: int,
    sender: bytes,
    to: bytes,
    data: bytes,
    nonce: int,
    base_fee_per_gas: int = 0,
) -> bytes:
    """Legacy EIP-155 transaction with the placeholder signature (r = s = 1)
    and the L1 block's base fee as its (never charged) gas price."""
    return rlp.encode(
        [
            relayer_nonce,
            base_fee_per_gas,
            SYSTEM_TRANSACTION_GAS_LIMIT,
            ACCESS_SPOKE,
            0,
            _relay_calldata(sender, to, data, nonce),
            domain_id * 2 + 35,
            1,
            1,
        ]
    )


def _on_domain_message_calldata_size(data: bytes) -> int:
    """onDomainMessage(uint64,address,bytes): selector, three head words, length word, padded data."""
    return 4 + 4 * 32 + (len(data) + 31) // 32 * 32


def _mapping_slot(key: bytes, slot: int) -> bytes:
    return keccak(_word(key) + _word(slot))


def _run(fresh_env: FreshEnv, blocks: list[BlockSpec], domains: list[int]):
    build_ledger(fresh_env.ledger, _with_committed_parent(blocks, sequencer=HUB))
    result = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=len(blocks) + 1,
        private_domain_keys=_key_files(fresh_env, tuple(domains)),
        private_domain_spokes={domain_id: ACCESS_SPOKE for domain_id in domains},
        private_domain_sequencer=HUB,
    )
    assert result.returncode == 0, (
        f"monad exited {result.returncode}:\n{result.stdout[-4000:]}\n"
        f"{result.stderr[-4000:]}"
    )
    return result


def _storage(dump: dict, domain_id: int, address: bytes) -> dict[str, str]:
    accounts = dump["domains"][domain_key(domain_id)]["accounts"]
    return accounts["0x" + address.hex()].get("storage", {})


def _storage_word(dump: dict, domain_id: int, address: bytes, slot: bytes | int) -> int:
    key = _word(slot) if isinstance(slot, int) else slot
    return int(_storage(dump, domain_id, address).get("0x" + key.hex(), "0x0"), 16)


def _assert_relayed_log(
    receipt,
    message_hash: bytes,
    sender: bytes,
    to: bytes,
    nonce: int,
    success: bool,
    source_chain_id: int = DEVNET_CHAIN_ID,
):
    logs = [log for log in receipt.logs if log.topics and log.topics[0] == L1_MESSAGE_RELAYED_SIGNATURE]
    assert len(logs) == 1, receipt
    (log,) = logs
    assert log.address == ACCESS_SPOKE
    assert log.topics == (L1_MESSAGE_RELAYED_SIGNATURE, message_hash, _word(sender), _word(to))
    assert log.data == _word(source_chain_id) + _word(nonce) + _word(int(success))


def test_l1_messages_are_delivered_after_sequenced_transactions(fresh_env: FreshEnv):
    receiver = _contract_address(INNER_ADDR, 0)
    plaintext_data = b"\x01\x02\x03"
    encrypted_data = bytes(range(40))
    ciphertext = encrypt_l1_message(DOMAIN_KEYS[DOMAIN_A], receiver, encrypted_data)

    # The receiver is deployed by a transaction sequenced in the SAME L1 block
    # as the messages: deliveries run after the block's sequenced transactions.
    # A live chain has a nonzero base fee, which gasless validation still
    # enforces as a fee-cap floor: the derived transactions must clear it.
    base_fee = 100_000_000_000
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        base_fee_per_gas=base_fee,
        txs=[
            _deploy_hub(max_fee_per_gas=base_fee),
            _register_domain(1, DOMAIN_A, max_fee_per_gas=base_fee),
            _sequence(
                0,
                DOMAIN_A,
                _inner_create(0, _init_code(RECEIVER_RUNTIME), max_fee_per_gas=base_fee),
                max_fee_per_gas=base_fee,
            ),
            _send_l1_message(0, DOMAIN_A, receiver, plaintext_data, key=ALICE_KEY, max_fee_per_gas=base_fee),
            _send_encrypted_l1_message(2, DOMAIN_A, ciphertext, key=HUB_DEPLOYER_KEY, max_fee_per_gas=base_fee),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    assert all(r.status == 1 for r in query_receipts(fresh_env.triedb, 2, 5))

    deploy_receipt = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0)
    first = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    second = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 2)
    assert deploy_receipt is not None and deploy_receipt.status == 1
    assert first is not None and first.status == 1
    assert second is not None and second.status == 1
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 3) is None
    assert first.gas_used > deploy_receipt.gas_used
    assert second.gas_used > first.gas_used

    first_hash = _message_hash(ALICE, receiver, plaintext_data, 0)
    second_hash = _message_hash(HUB_DEPLOYER, receiver, encrypted_data, 1)
    _assert_relayed_log(first, first_hash, ALICE, receiver, 0, True)
    _assert_relayed_log(second, second_hash, HUB_DEPLOYER, receiver, 1, True)

    # The stored transactions are the derived system transactions themselves.
    stored_first = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1)
    stored_second = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 2)
    assert stored_first.sender == SYSTEM_RELAYER
    assert stored_second.sender == SYSTEM_RELAYER
    assert stored_first.encoded == _expected_system_transaction(
        DOMAIN_A, 0, ALICE, receiver, plaintext_data, 0, base_fee
    )
    assert stored_second.encoded == _expected_system_transaction(
        DOMAIN_A, 1, HUB_DEPLOYER, receiver, encrypted_data, 1, base_fee
    )

    dump = dump_state(fresh_env.triedb, 2)
    accounts = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    assert int(accounts["0x" + SYSTEM_RELAYER.hex()]["nonce"]) == 2
    assert int(accounts["0x" + SYSTEM_RELAYER.hex()]["balance"]) == 0
    # The receiver saw the spoke as caller and the hub's `from` for each message.
    assert _storage_word(dump, DOMAIN_A, receiver, 0) == int.from_bytes(ACCESS_SPOKE, "big")
    assert _storage_word(dump, DOMAIN_A, receiver, _word(ALICE)) == _on_domain_message_calldata_size(plaintext_data)
    assert _storage_word(dump, DOMAIN_A, receiver, _word(HUB_DEPLOYER)) == _on_domain_message_calldata_size(encrypted_data)
    # The spoke consumed both hub nonces and recorded no failure.
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, SPOKE_NEXT_L1_NONCE_SLOT) == 2
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, _mapping_slot(first_hash, SPOKE_FAILED_L1_MESSAGES_SLOT)) == 0
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, _mapping_slot(second_hash, SPOKE_FAILED_L1_MESSAGES_SLOT)) == 0


def test_undeliverable_messages_leave_nonce_gaps_and_relayer_nonce_persists(fresh_env: FreshEnv):
    receiver = _contract_address(INNER_ADDR, 0)
    wrong_key = encrypt_l1_message(DOMAIN_KEYS[DOMAIN_B], receiver, b"\xaa")
    short_plaintext = encrypt_inner_transaction(DOMAIN_KEYS[DOMAIN_A], receiver[:10])

    first_block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _deploy_hub(),
            _register_domain(1, DOMAIN_A),
            _register_domain(2, DOMAIN_B),
            _sequence(0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(RECEIVER_RUNTIME))),
            _send_l1_message(0, DOMAIN_A, receiver, b"\x01"),  # DOMAIN_A nonce 0
            _send_encrypted_l1_message(1, DOMAIN_A, wrong_key),  # DOMAIN_A nonce 1: dropped
            _send_l1_message(2, DOMAIN_B, receiver, b"\x02"),  # DOMAIN_B: not served here
        ],
    )
    second_block = BlockSpec(
        seqno=2,
        timestamp=1_000_000_002,
        txs=[
            _send_l1_message(3, DOMAIN_A, receiver, b"\x03"),  # DOMAIN_A nonce 2
            _send_encrypted_l1_message(4, DOMAIN_A, short_plaintext),  # DOMAIN_A nonce 3: dropped
        ],
    )
    _run(fresh_env, [first_block, second_block], [DOMAIN_A])

    delivered = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert delivered is not None and delivered.status == 1
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 2) is None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, 0) is None
    _assert_relayed_log(delivered, _message_hash(ALICE, receiver, b"\x01", 0), ALICE, receiver, 0, True)

    later = query_domain_receipt(fresh_env.triedb, 3, DOMAIN_A, 0)
    assert later is not None and later.status == 1
    assert query_domain_receipt(fresh_env.triedb, 3, DOMAIN_A, 1) is None
    _assert_relayed_log(later, _message_hash(ALICE, receiver, b"\x03", 2), ALICE, receiver, 2, True)
    # The relayer nonce continues from the committed domain state.
    assert query_domain_transaction(fresh_env.triedb, 3, DOMAIN_A, 0).encoded == (
        _expected_system_transaction(DOMAIN_A, 1, ALICE, receiver, b"\x03", 2)
    )

    dump = dump_state(fresh_env.triedb, 3)
    accounts = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    assert int(accounts["0x" + SYSTEM_RELAYER.hex()]["nonce"]) == 2
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, SPOKE_NEXT_L1_NONCE_SLOT) == 3
    assert domain_key(DOMAIN_B) not in dump["domains"]


def test_failed_target_call_is_recorded_without_failing_the_delivery(fresh_env: FreshEnv):
    receiver = _contract_address(INNER_ADDR, 0)
    data = b"\x42"
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _deploy_hub(),
            _register_domain(1, DOMAIN_A),
            _sequence(0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(REVERTING_RECEIVER_RUNTIME))),
            _send_l1_message(0, DOMAIN_A, receiver, data),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    delivery = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert delivery is not None and delivery.status == 1
    message_hash = _message_hash(ALICE, receiver, data, 0)
    _assert_relayed_log(delivery, message_hash, ALICE, receiver, 0, False)

    dump = dump_state(fresh_env.triedb, 2)
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, SPOKE_NEXT_L1_NONCE_SLOT) == 1
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, _mapping_slot(message_hash, SPOKE_FAILED_L1_MESSAGES_SLOT)) == 1


def test_messages_without_a_spoke_do_not_abort_the_block(fresh_env: FreshEnv):
    """A message whose domain has no spoke code yet cannot be delivered:
    the access check fails closed, the system transaction reverts, and the
    L1 block still commits with the reverted delivery on record."""
    receiver = _contract_address(INNER_ADDR, 0)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _deploy_hub(),
            _register_domain(1, DOMAIN_B),
            _send_l1_message(0, DOMAIN_B, receiver, b"\x01"),
        ],
    )
    # The committed parent deploys the spokes at ACCESS_SPOKE; point the node
    # at an address that holds no code instead.
    build_ledger(fresh_env.ledger, _with_committed_parent([block], sequencer=HUB))
    empty_spoke = _contract_address(ALICE, 99)
    result = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=2,
        private_domain_keys=_key_files(fresh_env, (DOMAIN_B,)),
        private_domain_spokes={DOMAIN_B: empty_spoke},
        private_domain_sequencer=HUB,
    )
    assert result.returncode == 0, result.stderr[-4000:]

    delivery = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, 0)
    assert delivery is not None and delivery.status == 0 and delivery.logs == ()
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_B, 0).sender == SYSTEM_RELAYER


def test_gas_exhausting_target_is_still_recorded_as_failed(fresh_env: FreshEnv):
    """The spoke forwards a 2M stipend; the fixed system transaction gas limit
    leaves room to record the failure even when the target burns all of it."""
    receiver = _contract_address(INNER_ADDR, 0)
    data = b"\x43"
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _deploy_hub(),
            _register_domain(1, DOMAIN_A),
            _sequence(0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(GAS_EXHAUSTING_RECEIVER_RUNTIME))),
            _send_l1_message(0, DOMAIN_A, receiver, data),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    delivery = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert delivery is not None and delivery.status == 1
    message_hash = _message_hash(ALICE, receiver, data, 0)
    _assert_relayed_log(delivery, message_hash, ALICE, receiver, 0, False)
    dump = dump_state(fresh_env.triedb, 2)
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, SPOKE_NEXT_L1_NONCE_SLOT) == 1
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, _mapping_slot(message_hash, SPOKE_FAILED_L1_MESSAGES_SLOT)) == 1


def test_oversized_message_does_not_strand_later_messages(fresh_env: FreshEnv):
    """A payload whose intrinsic gas exceeds the fixed limit can never be
    delivered. It must not take a relayer nonce, or the deliveries behind it
    would fail their nonce checks and be lost as well."""
    receiver = _contract_address(INNER_ADDR, 0)
    oversized = b"\x01" * 200_000  # 16 gas/byte of intrinsic gas alone exceeds the limit
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _deploy_hub(),
            _register_domain(1, DOMAIN_A),
            _sequence(0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(RECEIVER_RUNTIME))),
            _l1_tx(
                0,
                HUB,
                _selector("sendL1Message(uint64,address,bytes)")
                + abi_encode(["uint64", "address", "bytes"], [DOMAIN_A, receiver, oversized]),
                ALICE_KEY,
                gas_limit=20_000_000,
            ),
            _send_l1_message(1, DOMAIN_A, receiver, b"\x02"),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    assert all(r.status == 1 for r in query_receipts(fresh_env.triedb, 2, 5))
    delivered = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert delivered is not None and delivered.status == 1
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 2) is None
    _assert_relayed_log(delivered, _message_hash(ALICE, receiver, b"\x02", 1), ALICE, receiver, 1, True)
    # The surviving delivery took relayer nonce 0: the oversized one never did.
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1).encoded == (
        _expected_system_transaction(DOMAIN_A, 0, ALICE, receiver, b"\x02", 1)
    )
    dump = dump_state(fresh_env.triedb, 2)
    accounts = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    assert int(accounts["0x" + SYSTEM_RELAYER.hex()]["nonce"]) == 1
    assert _storage_word(dump, DOMAIN_A, ACCESS_SPOKE, SPOKE_NEXT_L1_NONCE_SLOT) == 2
    assert _storage_word(dump, DOMAIN_A, receiver, _word(ALICE)) == _on_domain_message_calldata_size(b"\x02")


def test_two_served_domains_get_independent_deliveries(fresh_env: FreshEnv):
    receiver = _contract_address(INNER_ADDR, 0)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _deploy_hub(),
            _register_domain(1, DOMAIN_A),
            _register_domain(2, DOMAIN_B),
            _send_l1_message(0, DOMAIN_B, receiver, b"\xb0"),  # DOMAIN_B nonce 0, before DOMAIN_A's
            _sequence(0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(RECEIVER_RUNTIME))),
            _send_l1_message(1, DOMAIN_A, receiver, b"\xa0"),  # DOMAIN_A nonce 0
            _send_l1_message(2, DOMAIN_B, receiver, b"\xb1"),  # DOMAIN_B nonce 1
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A, DOMAIN_B])

    # DOMAIN_A: sequenced deployment first, then its single delivery.
    a_deploy = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0)
    a_delivery = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert a_deploy is not None and a_deploy.status == 1 and a_deploy.logs == ()
    assert a_delivery is not None and a_delivery.status == 1
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 2) is None
    _assert_relayed_log(a_delivery, _message_hash(ALICE, receiver, b"\xa0", 0), ALICE, receiver, 0, True)

    # DOMAIN_B: deliveries only, to an address that has no code there. The spoke records
    # such deliveries as failed (retryable once the target is deployed) and still consumes
    # the hub nonce; the relayer nonces are B's own.
    for index, (payload, nonce) in enumerate([(b"\xb0", 0), (b"\xb1", 1)]):
        receipt = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, index)
        assert receipt is not None and receipt.status == 1
        _assert_relayed_log(receipt, _message_hash(ALICE, receiver, payload, nonce), ALICE, receiver, nonce, False)
        assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_B, index).encoded == (
            _expected_system_transaction(DOMAIN_B, index, ALICE, receiver, payload, nonce)
        )
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, 2) is None

    dump = dump_state(fresh_env.triedb, 2)
    for domain_id, expected in ((DOMAIN_A, 1), (DOMAIN_B, 2)):
        accounts = dump["domains"][domain_key(domain_id)]["accounts"]
        assert int(accounts["0x" + SYSTEM_RELAYER.hex()]["nonce"]) == expected
        assert _storage_word(dump, domain_id, ACCESS_SPOKE, SPOKE_NEXT_L1_NONCE_SLOT) == expected
    for payload, nonce in ((b"\xb0", 0), (b"\xb1", 1)):
        codeless_hash = _message_hash(ALICE, receiver, payload, nonce)
        assert _storage_word(dump, DOMAIN_B, ACCESS_SPOKE, _mapping_slot(codeless_hash, SPOKE_FAILED_L1_MESSAGES_SLOT)) == 1
