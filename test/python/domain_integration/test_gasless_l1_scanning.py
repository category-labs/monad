"""End-to-end coverage for L1-sequenced gasless domain blocks.

Every test runs against the real hub: the committed parent block deploys it,
registers both domains and seeds their spokes, and each sequencing call pays
`gas * DOMAIN_GAS_PRICE` for the gas its domain transaction declares.
"""

from __future__ import annotations

import rlp
from eth_abi import encode as abi_encode
from eth_account import Account
from eth_keys import keys
from eth_utils import keccak

from .abi import sequence_to_domain_calldata
from .block_builder import BlockSpec, build_ledger
from .conftest import FreshEnv
from .constants import DEV_ACCOUNTS, DEVNET_CHAIN_ID
from .hpke import encrypt_inner_transaction, write_private_key_files
from .domain_hub_bytecode import DOMAIN_HUB_CREATION_CODE
from .domain_spoke_bytecode import DOMAIN_SPOKE_CREATION_CODE
from .monad_runner import (
    query_domain_receipt,
    query_domain_transaction,
    query_domain_transaction_and_receipt_by_hash,
    query_domain_transaction_location,
    query_domain_transaction_sender,
    query_receipts,
    run_monad,
)
from .state_dump import dump_state
from .state_root import (
    AccountState,
    EMPTY_ROOT,
    compute_state_root,
    validate_state_root,
)
from .tx import Tx, domain_chain_id, domain_key, sign_tx

DOMAIN_A = domain_chain_id(0x51)
DOMAIN_B = domain_chain_id(0x52)
DOMAIN_KEYS = {
    DOMAIN_A: (1).to_bytes(32, "big"),
    DOMAIN_B: (2).to_bytes(32, "big"),
}
OUTER_ADDR, OUTER_KEY = DEV_ACCOUNTS[0]
INNER_ADDR, INNER_KEY = DEV_ACCOUNTS[1]
HUB_DEPLOYER, HUB_DEPLOYER_KEY = DEV_ACCOUNTS[2]
FEE_RECIPIENT = DEV_ACCOUNTS[4][0]
ACCESS_DEPLOYER, ACCESS_DEPLOYER_KEY = DEV_ACCOUNTS[5]

# Mirrors DomainHub.DOMAIN_GAS_PRICE.
DOMAIN_GAS_PRICE = 50_000_000_000

INNER_SSTORE_RUNTIME = b"\x33\x60\x00\x55\x00"
INNER_LOG_RUNTIME = (
    b"\x60\x2a\x60\x00\x52"  # mstore(0, 0x2a)
    b"\x60\x7b\x60\x20\x60\x00\xa1\x00"  # log1(0, 32, 0x7b)
)
DOMAIN_STATE_UPDATED_SIGNATURE = keccak(
    text="DomainStateUpdated(uint64,uint256,uint64,bytes32,bytes32)"
)


def _init_code(runtime: bytes) -> bytes:
    size = len(runtime)
    return (
        b"\x60"
        + bytes([size])
        + b"\x60\x0c\x60\x00\x39"
        + b"\x60"
        + bytes([size])
        + b"\x60\x00\xf3"
        + runtime
    )


def _zero_data_subcall(
    address: bytes, opcode: int, *, output_size: int = 0
) -> bytes:
    """Call address with 20,000 gas and empty input/output in static context."""
    assert len(address) == 20
    assert opcode in (0xF4, 0xFA)  # DELEGATECALL or STATICCALL
    assert 0 <= output_size <= 0xFF
    return (
        b"\x60"
        + bytes([output_size])
        + b"\x60\x00" * 3
        + b"\x73"
        + address
        + b"\x61\x4e\x20"
        + bytes([opcode])
    )


def _domain_state_updated_runtime(domain_id: int) -> bytes:
    """Return calldata as event data with the configured domain as topic 1."""
    assert domain_id.bit_length() <= 64
    return (
        b"\x60\x80\x60\x00\x60\x00\x37"  # calldatacopy(0, 0, 128)
        + b"\x7f"
        + domain_id.to_bytes(32, "big")
        + b"\x7f"
        + DOMAIN_STATE_UPDATED_SIGNATURE
        + b"\x60\x80\x60\x00\xa2\x00"  # log2(0, 128, signature, domain)
    )


def _domain_state_updated_data(block_number: int, state_root: bytes) -> bytes:
    assert block_number.bit_length() <= 64
    assert len(state_root) == 32
    return b"".join(
        (
            (7).to_bytes(32, "big"),
            block_number.to_bytes(32, "big"),
            state_root,
            (9).to_bytes(32, "big"),
        )
    )


def _contract_address(sender: bytes, nonce: int) -> bytes:
    return keccak(rlp.encode([sender, nonce]))[12:]


HUB = _contract_address(HUB_DEPLOYER, 0)
ACCESS_SPOKE = _contract_address(ACCESS_DEPLOYER, 0)
ACCESS_TARGET = _contract_address(ACCESS_SPOKE, 1)
ACCESS_TARGET_SELECTOR = keccak(text="writeFor(address)")[:4]
ACCESS_TARGET_RUNTIME = b"\x33\x60\x00\x55\x00"  # sstore(0, caller)
# keccak of the pinned DomainSpoke runtime as deployed on DOMAIN_A by the committed
# parent, i.e. with the immutables (DOMAIN_A, DEVNET_CHAIN_ID, HUB).
ACCESS_SPOKE_CODE_HASH_DOMAIN_A = bytes.fromhex(
    "4070a9c0dccd003c949555388da5450b81a1ad6ca14677d1104426a30f37cf76"
)
# Balance of every dev account in MONAD_DEVNET_ALLOC.
GENESIS_BALANCE = 10**38

STATE_TRANSITION_TYPEHASH = keccak(
    text="StateTransition(uint64 domainChainId,uint256 stateNonce,uint64 domainBlockNumber,"
    "bytes32 newStateRoot,bytes32 domainAnchor)"
)


def _abi_word(value: int) -> bytes:
    return value.to_bytes(32, "big")


def _selector(signature: str) -> bytes:
    return keccak(text=signature)[:4]


def _domain_spoke_init_code(domain_id: int, hub: bytes) -> bytes:
    """Pinned DomainSpoke bytecode plus (domainChainId, l1ChainId, hub)."""
    return (
        DOMAIN_SPOKE_CREATION_CODE
        + _abi_word(domain_id)
        + _abi_word(DEVNET_CHAIN_ID)
        + hub.rjust(32, b"\x00")
    )


def _fees_collected(dump: dict) -> int:
    """Wei the fee recipient has received, from the L1 state dump."""
    return int(dump["accounts"]["0x" + FEE_RECIPIENT.hex()]["balance"]) - GENESIS_BALANCE


def _l1_tx(
    nonce: int,
    to: bytes | None,
    data: bytes,
    key: bytes,
    *,
    value: int = 0,
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
            value=value,
            data=data,
        ),
        key,
    )


def _deploy_hub():
    return _l1_tx(0, None, DOMAIN_HUB_CREATION_CODE, HUB_DEPLOYER_KEY, gas_limit=8_000_000)


def _register_domain(nonce: int, domain_id: int):
    """registerDomain with the hub deployer as sole validator and a one-block checkpoint schedule."""
    data = _selector("registerDomain(uint64,address[],uint256,address,bytes,uint64)") + abi_encode(
        ["uint64", "address[]", "uint256", "address", "bytes", "uint64"],
        [domain_id, [HUB_DEPLOYER], 1, FEE_RECIPIENT, b"", 1],
    )
    return _l1_tx(nonce, HUB, data, HUB_DEPLOYER_KEY)


def _state_transition_signature(
    domain_id: int, state_nonce: int, block_number: int, state_root: bytes, anchor: bytes = bytes(32)
) -> bytes:
    """The hub deployer's EIP-712 signature over a state transition, as a validator."""
    domain_separator = keccak(
        abi_encode(
            ["bytes32", "bytes32", "bytes32", "uint256", "address"],
            [
                keccak(text="EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
                keccak(text="MonadDomainHub"),
                keccak(text="1"),
                DEVNET_CHAIN_ID,
                HUB,
            ],
        )
    )
    struct_hash = keccak(
        abi_encode(
            ["bytes32", "uint64", "uint256", "uint64", "bytes32", "bytes32"],
            [STATE_TRANSITION_TYPEHASH, domain_id, state_nonce, block_number, state_root, anchor],
        )
    )
    signature = keys.PrivateKey(HUB_DEPLOYER_KEY).sign_msg_hash(keccak(b"\x19\x01" + domain_separator + struct_hash))
    return signature.r.to_bytes(32, "big") + signature.s.to_bytes(32, "big") + bytes([signature.v + 27])


def _submit_state_signature(nonce: int, domain_id: int, state_nonce: int, block_number: int, state_root: bytes):
    data = _selector("submitStateSignature(uint64,uint64,bytes32,bytes32,bytes)") + abi_encode(
        ["uint64", "uint64", "bytes32", "bytes32", "bytes"],
        [
            domain_id,
            block_number,
            state_root,
            bytes(32),
            _state_transition_signature(domain_id, state_nonce, block_number, state_root),
        ],
    )
    return _l1_tx(nonce, HUB, data, HUB_DEPLOYER_KEY)


def _deploy_contract_calldata(init_code: bytes, policy_owner: bytes) -> bytes:
    selector = keccak(text="deployContract(bytes,address)")[:4]
    padding = (-len(init_code)) % 32
    return (
        selector
        + _abi_word(64)
        + policy_owner.rjust(32, b"\x00")
        + _abi_word(len(init_code))
        + init_code
        + bytes(padding)
    )


def _set_access_policy_calldata(target: bytes, policy: bytes) -> bytes:
    return _selector("setAccessPolicy(address,address)") + target.rjust(32, b"\x00") + policy.rjust(32, b"\x00")


def _caller_policy_runtime(allowed: bytes) -> bytes:
    """canCall(caller, context, data) returning true only for `allowed`."""
    return b"\x60\x04\x35\x73" + allowed + b"\x14\x60\x00\x52\x60\x20\x60\x00\xf3"


def _access_target_calldata(subject: bytes) -> bytes:
    return ACCESS_TARGET_SELECTOR + subject.rjust(32, b"\x00")


def _committed_parent_transactions() -> list[tuple[Tx, bytes]]:
    """Deploy the hub, register both domains and seed their spokes."""
    transactions = [_deploy_hub(), _register_domain(1, DOMAIN_A), _register_domain(2, DOMAIN_B)]
    for outer_nonce, domain_id in enumerate((DOMAIN_A, DOMAIN_B)):
        deploy = sign_tx(
            Tx(
                nonce=0,
                gas_limit=4_000_000,
                max_priority_fee_per_gas=0,
                max_fee_per_gas=0,
                to=None,
                value=0,
                data=_domain_spoke_init_code(domain_id, HUB),
                chain_id=domain_id,
            ),
            ACCESS_DEPLOYER_KEY,
        )
        encrypted = encrypt_inner_transaction(DOMAIN_KEYS[domain_id], deploy)
        transactions.append(
            _l1_tx(
                outer_nonce,
                HUB,
                sequence_to_domain_calldata(domain_id, encrypted),
                ACCESS_DEPLOYER_KEY,
                value=4_000_000 * DOMAIN_GAS_PRICE,
            )
        )
    return transactions


def _inner(
    *,
    nonce: int,
    to: bytes | None,
    data: bytes = b"",
    value: int = 0,
    domain_id: int = DOMAIN_A,
    gas_limit: int = 1_000_000,
) -> bytes:
    return sign_tx(
        Tx(
            nonce=nonce,
            gas_limit=gas_limit,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=0,
            to=to,
            value=value,
            data=data,
            chain_id=domain_id,
        ),
        INNER_KEY,
    )


def _outer(
    nonce: int,
    domain_id: int,
    payload: bytes,
    paid_gas: int = 1_500_000,
    *,
    receiver_scalar: bytes | None = None,
    frame_version: int = 1,
) -> tuple[Tx, bytes]:
    encrypted = encrypt_inner_transaction(
        (
            receiver_scalar
            if receiver_scalar is not None
            else DOMAIN_KEYS[domain_id]
        ),
        payload,
        frame_version=frame_version,
    )
    return _outer_raw(nonce, domain_id, encrypted, paid_gas)


def _outer_raw(
    nonce: int,
    domain_id: int,
    payload: bytes,
    paid_gas: int = 1_500_000,
    *,
    l1_gas_limit: int = 1_500_000,
) -> tuple[Tx, bytes]:
    """sequenceToDomain through the hub, paying for `paid_gas` of domain gas."""
    return _l1_tx(
        nonce,
        HUB,
        sequence_to_domain_calldata(domain_id, payload),
        OUTER_KEY,
        value=paid_gas * DOMAIN_GAS_PRICE,
        gas_limit=l1_gas_limit,
    )


def _key_files(fresh_env: FreshEnv, domains: tuple[int, ...]):
    return write_private_key_files(
        fresh_env.root / "domain-keys",
        {domain_id: DOMAIN_KEYS[domain_id] for domain_id in domains},
    )


def _unprotected_legacy_inner(*, nonce: int, to: bytes) -> bytes:
    """Return a recoverable legacy transaction without an EIP-155 chain ID."""
    signed = Account.sign_transaction(
        {
            "nonce": nonce,
            "gasPrice": 0,
            "gas": 100_000,
            "to": to,
            "value": 0,
            "data": b"",
        },
        INNER_KEY.hex(),
    )
    encoded = bytes(signed.raw_transaction)
    assert encoded[0] >= 0xC0
    assert int.from_bytes(rlp.decode(encoded)[6], "big") in (27, 28)
    return encoded


def _with_committed_parent(blocks: list[BlockSpec]) -> list[BlockSpec]:
    """Prepend the protocol setup block and shift test blocks by one; private
    domain execution is based on the committed L1 parent."""
    assert blocks
    shifted = [
        BlockSpec(
            seqno=block.seqno + 1,
            txs=block.txs,
            timestamp=block.timestamp,
            gas_limit=block.gas_limit,
            base_fee_per_gas=block.base_fee_per_gas,
            beneficiary=block.beneficiary,
            extra_data=block.extra_data,
            difficulty=block.difficulty,
        )
        for block in blocks
    ]
    return [
        BlockSpec(
            seqno=1,
            timestamp=max(0, blocks[0].timestamp - 1),
            txs=_committed_parent_transactions(),
        ),
        *shifted,
    ]


def _run(fresh_env: FreshEnv, blocks: list[BlockSpec], domains: list[int]):
    build_ledger(fresh_env.ledger, _with_committed_parent(blocks))
    result = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=len(blocks) + 1,
        private_domain_keys=_key_files(fresh_env, tuple(domains)),
        private_domain_spokes={
            domain_id: ACCESS_SPOKE for domain_id in domains
        },
        private_domain_sequencer=HUB,
    )
    assert result.returncode == 0, (
        f"monad exited {result.returncode}:\n{result.stdout[-4000:]}\n"
        f"{result.stderr[-4000:]}"
    )
    return result


def test_gasless_deploy_and_call(fresh_env: FreshEnv):
    contract = _contract_address(INNER_ADDR, 0)
    deploy = _inner(nonce=0, to=None, data=_init_code(INNER_SSTORE_RUNTIME))
    call = _inner(nonce=1, to=contract)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(0, DOMAIN_A, deploy),
            _outer(1, DOMAIN_A, call),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    assert all(r.status == 1 for r in query_receipts(fresh_env.triedb, 2, 2))
    assert all(r.status == 1 for r in query_receipts(fresh_env.triedb, 1, 5))
    receipt0 = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0)
    receipt1 = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert receipt0 is not None and receipt0.status == 1 and receipt0.gas_used > 0
    assert receipt1 is not None and receipt1.status == 1
    assert receipt1.gas_used > receipt0.gas_used
    assert (
        query_domain_transaction_sender(fresh_env.triedb, 2, DOMAIN_A, 0) == INNER_ADDR
    )
    assert (
        query_domain_transaction_sender(fresh_env.triedb, 2, DOMAIN_A, 1) == INNER_ADDR
    )
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0).encoded == deploy
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1).encoded == call

    dump = dump_state(fresh_env.triedb, 2)
    validate_state_root(dump)
    accounts = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    assert int(accounts["0x" + INNER_ADDR.hex()]["nonce"]) == 2
    assert int(accounts["0x" + INNER_ADDR.hex()]["balance"]) == 0
    assert (
        accounts["0x" + contract.hex()]["code_hash"]
        == "0x" + keccak(INNER_SSTORE_RUNTIME).hex()
    )
    assert accounts["0x" + contract.hex()]["storage"]["0x" + bytes(32).hex()] == (
        "0x" + INNER_ADDR.rjust(32, b"\x00").hex()
    )


def test_domain_spoke_enforces_custom_access_rule(fresh_env: FreshEnv):
    policy = _contract_address(INNER_ADDR, 0)
    deploy_target = sign_tx(
        Tx(
            nonce=1,
            gas_limit=1_000_000,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=0,
            to=ACCESS_SPOKE,
            value=0,
            data=_deploy_contract_calldata(
                _init_code(ACCESS_TARGET_RUNTIME), ACCESS_DEPLOYER
            ),
            chain_id=DOMAIN_A,
        ),
        ACCESS_DEPLOYER_KEY,
    )
    deploy_policy = _inner(nonce=0, to=None, data=_init_code(_caller_policy_runtime(INNER_ADDR)))
    configure_target = sign_tx(
        Tx(
            nonce=2,
            gas_limit=1_000_000,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=0,
            to=ACCESS_SPOKE,
            value=0,
            data=_set_access_policy_calldata(ACCESS_TARGET, policy),
            chain_id=DOMAIN_A,
        ),
        ACCESS_DEPLOYER_KEY,
    )
    denied = sign_tx(
        Tx(
            nonce=0,
            gas_limit=1_000_000,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=0,
            to=ACCESS_TARGET,
            value=0,
            data=_access_target_calldata(INNER_ADDR),
            chain_id=DOMAIN_A,
        ),
        OUTER_KEY,
    )
    allowed = _inner(
        nonce=1,
        to=ACCESS_TARGET,
        data=_access_target_calldata(INNER_ADDR),
    )
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(0, DOMAIN_A, deploy_target),
            _outer(1, DOMAIN_A, deploy_policy),
            _outer(2, DOMAIN_A, configure_target),
            _outer(3, DOMAIN_A, denied),
            _outer(4, DOMAIN_A, allowed),
        ],
    )

    _run(fresh_env, [block], [DOMAIN_A])

    receipts = [
        query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, index) for index in range(5)
    ]
    assert all(receipt is not None for receipt in receipts)
    assert [receipt.status for receipt in receipts] == [1, 1, 1, 0, 1]
    accounts = dump_state(fresh_env.triedb, 2)["domains"][domain_key(DOMAIN_A)][
        "accounts"
    ]
    target = accounts["0x" + ACCESS_TARGET.hex()]
    assert target["code_hash"] == "0x" + keccak(ACCESS_TARGET_RUNTIME).hex()
    assert target["storage"]["0x" + bytes(32).hex()] == (
        "0x" + INNER_ADDR.rjust(32, b"\x00").hex()
    )


def test_domain_access_check_reverts_on_second_hop_call(fresh_env: FreshEnv):
    policy_spoke = _contract_address(INNER_ADDR, 0)
    policy_leaf = _contract_address(INNER_ADDR, 1)
    target = _contract_address(INNER_ADDR, 2)
    grandchild = bytes.fromhex("66" * 20)

    # canCall makes an allowed direct call and propagates its ABI-encoded bool.
    policy_runtime = (
        _zero_data_subcall(policy_leaf, 0xFA, output_size=32)
        + b"\x50"
        + b"\x60\x20\x60\x00\xf3"
    )
    # The direct callee returns the prohibited second-hop DELEGATECALL status
    # as data while still succeeding. canCall therefore returns canonical
    # false and the target transaction reverts.
    leaf_runtime = (
        _zero_data_subcall(grandchild, 0xF4)
        + b"\x60\x00\x52\x60\x20\x60\x00\xf3"
    )
    target_runtime = b"\x60\x01\x60\x00\x55\x00"  # sstore(0, 1)

    deploy_block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(
                0,
                DOMAIN_A,
                _inner(nonce=0, to=None, data=_init_code(policy_runtime)),
            ),
            _outer(
                1,
                DOMAIN_A,
                _inner(nonce=1, to=None, data=_init_code(leaf_runtime)),
            ),
            _outer(
                2,
                DOMAIN_A,
                _inner(nonce=2, to=None, data=_init_code(target_runtime)),
            ),
        ],
    )
    call_block = BlockSpec(
        seqno=2,
        timestamp=1_000_000_002,
        txs=[_outer(3, DOMAIN_A, _inner(nonce=3, to=target))],
    )
    build_ledger(
        fresh_env.ledger,
        _with_committed_parent([deploy_block, call_block]),
    )

    keys = _key_files(fresh_env, (DOMAIN_A,))
    deployed = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=2,
        private_domain_keys=keys,
        private_domain_spokes={DOMAIN_A: ACCESS_SPOKE},
        private_domain_sequencer=HUB,
    )
    assert deployed.returncode == 0, deployed.stderr[-4000:]
    deploy_receipts = [
        query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, index)
        for index in range(3)
    ]
    assert all(receipt is not None for receipt in deploy_receipts)
    assert [receipt.status for receipt in deploy_receipts] == [1, 1, 1]

    executed = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=1,
        private_domain_keys=keys,
        private_domain_spokes={DOMAIN_A: policy_spoke},
        private_domain_sequencer=HUB,
    )
    assert executed.returncode == 0, executed.stderr[-4000:]

    receipt = query_domain_receipt(fresh_env.triedb, 3, DOMAIN_A, 0)
    assert receipt is not None and receipt.status == 0 and receipt.gas_used > 0
    accounts = dump_state(fresh_env.triedb, 3)["domains"][domain_key(DOMAIN_A)][
        "accounts"
    ]
    assert accounts["0x" + policy_spoke.hex()]["code_hash"] == (
        "0x" + keccak(policy_runtime).hex()
    )
    assert accounts["0x" + policy_leaf.hex()]["code_hash"] == (
        "0x" + keccak(leaf_runtime).hex()
    )
    target_account = accounts["0x" + target.hex()]
    assert target_account["code_hash"] == "0x" + keccak(target_runtime).hex()
    assert "storage" not in target_account


def test_domain_state_update_validates_exact_historical_root(
    fresh_env: FreshEnv,
):
    # A successful zero-value call increments the sender nonce without leaving
    # an empty recipient behind. Build the expected domain tries from that
    # protocol state, independently of the database under test.
    def expected_root(inner_nonce: int) -> bytes:
        return compute_state_root(
            {
                INNER_ADDR: AccountState(nonce=inner_nonce),
                ACCESS_DEPLOYER: AccountState(nonce=1),
                ACCESS_SPOKE: AccountState(nonce=1, code_hash=ACCESS_SPOKE_CODE_HASH_DOMAIN_A),
            }
        )

    root_at_2 = expected_root(1)
    root_at_3 = expected_root(2)
    assert EMPTY_ROOT not in (root_at_2, root_at_3)
    bad_root = bytes([root_at_2[0] ^ 1]) + root_at_2[1:]

    blocks = _with_committed_parent(
        [
            BlockSpec(seqno=1, timestamp=1_000_000_001, txs=[_outer(0, DOMAIN_A, _inner(nonce=0, to=OUTER_ADDR))]),
            # The sole validator attests a wrong root for domain block 2 while
            # block 3 advances the domain again.
            BlockSpec(
                seqno=2,
                timestamp=1_000_000_002,
                txs=[
                    _outer(1, DOMAIN_A, _inner(nonce=1, to=OUTER_ADDR)),
                    _submit_state_signature(3, DOMAIN_A, 0, 2, bad_root),
                ],
            ),
            BlockSpec(seqno=3, timestamp=1_000_000_003, txs=[_submit_state_signature(4, DOMAIN_A, 1, 3, root_at_3)]),
        ]
    )
    build_ledger(fresh_env.ledger, blocks)
    common = {
        "private_domain_keys": _key_files(fresh_env, (DOMAIN_A,)),
        "private_domain_spokes": {DOMAIN_A: ACCESS_SPOKE},
        "private_domain_sequencer": HUB,
    }
    result = run_monad(fresh_env.ledger, fresh_env.triedb, nblocks=2, **common)
    assert result.returncode == 0, result.stderr[-4000:]
    domain_dump = dump_state(fresh_env.triedb, 2)["domains"][domain_key(DOMAIN_A)]
    assert bytes.fromhex(domain_dump["state_root"][2:]) == root_at_2

    # A root that disagrees with local history is reported as an error; the
    # block carrying the attestation still executes and commits.
    mismatched = run_monad(fresh_env.ledger, fresh_env.triedb, nblocks=1, **common)
    mismatched_output = mismatched.stdout + "\n" + mismatched.stderr
    assert mismatched.returncode == 0, mismatched_output[-4000:]
    assert query_receipts(fresh_env.triedb, 3, 2)[1].status == 1
    assert "state root mismatch at finalized block 2" in mismatched_output
    assert root_at_2.hex() in mismatched_output
    assert bad_root.hex() in mismatched_output
    assert bytes.fromhex(dump_state(fresh_env.triedb, 3)["domains"][domain_key(DOMAIN_A)]["state_root"][2:]) == root_at_3

    validated = run_monad(fresh_env.ledger, fresh_env.triedb, nblocks=1, **common)
    validated_output = validated.stdout + "\n" + validated.stderr
    assert validated.returncode == 0, validated_output[-4000:]
    assert query_receipts(fresh_env.triedb, 4, 1)[0].status == 1
    assert "Validated DomainStateUpdated for domain" in validated_output
    assert root_at_3.hex() in validated_output


def test_gasless_runtime_revert_is_retained(fresh_env: FreshEnv):
    reverting_runtime = b"\x60\x00\x60\x00\xfd"
    contract = _contract_address(INNER_ADDR, 0)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(
                0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(reverting_runtime))
            ),
            _outer(1, DOMAIN_A, _inner(nonce=1, to=contract)),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0).status == 1
    receipt = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert receipt is not None and receipt.status == 0 and receipt.gas_used > 0
    assert (
        query_domain_transaction_sender(fresh_env.triedb, 2, DOMAIN_A, 1) == INNER_ADDR
    )
    dump = dump_state(fresh_env.triedb, 2)
    accounts = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    assert int(accounts["0x" + INNER_ADDR.hex()]["nonce"]) == 2
    assert accounts["0x" + contract.hex()]["code_hash"] == (
        "0x" + keccak(reverting_runtime).hex()
    )


def test_decoded_invalid_transactions_are_not_persisted(
    fresh_env: FreshEnv,
):
    unpaid_gas = _inner(nonce=0, to=OUTER_ADDR, gas_limit=500_001)
    nonzero_value = _inner(nonce=0, to=OUTER_ADDR, value=1)
    bad_nonce = _inner(nonce=9, to=OUTER_ADDR)
    signed = _inner(nonce=0, to=OUTER_ADDR)
    signature_fields = rlp.decode(signed[1:])
    signature_fields[-2] = b""
    signature_fields[-1] = b""
    invalid_signature = b"\x02" + rlp.encode(signature_fields)
    contract = _contract_address(INNER_ADDR, 0)
    deploy = _inner(nonce=0, to=None, data=_init_code(INNER_SSTORE_RUNTIME))
    wrong_chain = _inner(nonce=1, to=contract, domain_id=DOMAIN_B)
    call = _inner(nonce=1, to=contract)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(0, DOMAIN_A, b"not rlp"),
            _outer(1, DOMAIN_A, unpaid_gas, paid_gas=500_000),
            _outer(2, DOMAIN_A, nonzero_value),
            _outer(3, DOMAIN_A, bad_nonce),
            _outer(4, DOMAIN_A, invalid_signature),
            _outer(5, DOMAIN_A, deploy),
            _outer(6, DOMAIN_A, wrong_chain),
            _outer(7, DOMAIN_A, call),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    invalid = [
        unpaid_gas,
        nonzero_value,
        bad_nonce,
        invalid_signature,
        wrong_chain,
    ]
    for transaction in invalid:
        assert (
            query_domain_transaction_location(
                fresh_env.triedb, 2, DOMAIN_A, keccak(transaction)
            )
            is None
        )

    deploy_receipt = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert deploy_receipt is not None and deploy_receipt.status == 1
    assert deploy_receipt.gas_used > 0
    assert (
        query_domain_transaction_sender(fresh_env.triedb, 2, DOMAIN_A, 0) == INNER_ADDR
    )

    call_receipt = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1)
    assert call_receipt is not None and call_receipt.status == 1
    assert call_receipt.gas_used > deploy_receipt.gas_used
    assert query_domain_transaction_location(
        fresh_env.triedb, 2, DOMAIN_A, keccak(deploy)
    ) == (2, 0)
    assert query_domain_transaction_location(
        fresh_env.triedb, 2, DOMAIN_A, keccak(call)
    ) == (2, 1)
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 2) is None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 2) is None


def test_all_decoded_invalid_transactions_leave_empty_tables(
    fresh_env: FreshEnv,
):
    invalid = _inner(nonce=0, to=OUTER_ADDR, value=1)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[_outer(0, DOMAIN_A, invalid)],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0) is None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0) is None
    assert (
        query_domain_transaction_location(fresh_env.triedb, 2, DOMAIN_A, keccak(invalid))
        is None
    )


def test_payload_decode_and_envelope_eligibility_boundaries(
    fresh_env: FreshEnv,
):
    exact_gas = _inner(nonce=0, to=OUTER_ADDR, gas_limit=300_000)
    trailing_rlp = exact_gas + b"\x00"
    no_chain_id = _unprotected_legacy_inner(nonce=0, to=OUTER_ADDR)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(0, DOMAIN_A, b""),
            _outer(1, DOMAIN_A, trailing_rlp),
            _outer(2, DOMAIN_A, no_chain_id),
            # gas_limit == purchased gas is eligible.
            _outer(3, DOMAIN_A, exact_gas, paid_gas=300_000),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    stored = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert stored is not None and stored.encoded == exact_gas
    receipt = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert receipt is not None and receipt.status == 1
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1) is None
    for rejected in (trailing_rlp, no_chain_id):
        assert (
            query_domain_transaction_location(
                fresh_env.triedb, 2, DOMAIN_A, keccak(rejected)
            )
            is None
        )


def test_hpke_authentication_and_framing_failures_are_dropped(
    fresh_env: FreshEnv,
):
    inner = _inner(nonce=0, to=OUTER_ADDR)
    tampered = bytearray(encrypt_inner_transaction(DOMAIN_KEYS[DOMAIN_A], inner))
    tampered[-1] ^= 1
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer_raw(0, DOMAIN_A, inner),
            _outer(1, DOMAIN_A, inner, receiver_scalar=DOMAIN_KEYS[DOMAIN_B]),
            _outer(2, DOMAIN_A, inner, frame_version=2),
            _outer_raw(3, DOMAIN_A, bytes(tampered)),
            _outer(4, DOMAIN_A, inner),
        ],
    )

    result = _run(fresh_env, [block], [DOMAIN_A])

    output = result.stdout + "\n" + result.stderr
    assert (
        output.count("Dropped private domain payload after decryption failed") == 4
    )
    stored = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert stored is not None and stored.encoded == inner
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1) is None


def test_inner_nonce_blocks_identical_ciphertext_replay(fresh_env: FreshEnv):
    inner = _inner(nonce=0, to=OUTER_ADDR)
    encrypted = encrypt_inner_transaction(DOMAIN_KEYS[DOMAIN_A], inner)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer_raw(0, DOMAIN_A, encrypted),
            _outer_raw(1, DOMAIN_A, encrypted),
        ],
    )

    _run(fresh_env, [block], [DOMAIN_A])

    stored = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert stored is not None and stored.encoded == inner
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1) is None
    accounts = dump_state(fresh_env.triedb, 2)["domains"][domain_key(DOMAIN_A)][
        "accounts"
    ]
    assert int(accounts["0x" + INNER_ADDR.hex()]["nonce"]) == 1


def test_ciphertext_can_be_resubmitted_with_a_sufficient_fee(fresh_env: FreshEnv):
    inner = _inner(nonce=0, to=OUTER_ADDR, gas_limit=300_000)
    encrypted = encrypt_inner_transaction(DOMAIN_KEYS[DOMAIN_A], inner)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer_raw(0, DOMAIN_A, encrypted, paid_gas=299_999),
            _outer_raw(1, DOMAIN_A, encrypted, paid_gas=300_000),
        ],
    )

    _run(fresh_env, [block], [DOMAIN_A])

    stored = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert stored is not None and stored.encoded == inner
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1) is None
    # Both fees reached the recipient: an unpaid-for transaction is not refunded.
    assert _fees_collected(dump_state(fresh_env.triedb, 2)) == (4_000_000 * 2 + 299_999 + 300_000) * DOMAIN_GAS_PRICE


def test_out_of_gas_and_logs_are_persisted_as_executed_receipts(
    fresh_env: FreshEnv,
):
    storage_contract = _contract_address(INNER_ADDR, 0)
    log_contract = _contract_address(INNER_ADDR, 2)
    deploy_storage = _inner(nonce=0, to=None, data=_init_code(INNER_SSTORE_RUNTIME))
    out_of_gas = _inner(nonce=1, to=storage_contract, gas_limit=22_000)
    deploy_logger = _inner(nonce=2, to=None, data=_init_code(INNER_LOG_RUNTIME))
    emit_log = _inner(nonce=3, to=log_contract)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(0, DOMAIN_A, deploy_storage),
            _outer(1, DOMAIN_A, out_of_gas),
            _outer(2, DOMAIN_A, deploy_logger),
            _outer(3, DOMAIN_A, emit_log),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    receipts = [query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, i) for i in range(4)]
    assert all(receipt is not None for receipt in receipts)
    deploy_receipt, oog_receipt, logger_receipt, log_receipt = receipts
    assert deploy_receipt is not None and deploy_receipt.status == 1
    assert oog_receipt is not None and oog_receipt.status == 0
    assert oog_receipt.gas_used - deploy_receipt.gas_used == 22_000
    assert logger_receipt is not None and logger_receipt.status == 1
    assert logger_receipt.gas_used > oog_receipt.gas_used
    assert log_receipt is not None and log_receipt.status == 1
    assert log_receipt.gas_used > logger_receipt.gas_used
    assert len(log_receipt.logs) == 1
    assert log_receipt.logs[0].address == log_contract
    assert log_receipt.logs[0].data == b"\x00" * 31 + b"\x2a"
    assert log_receipt.logs[0].topics == (b"\x00" * 31 + b"\x7b",)

    assert query_domain_transaction_location(
        fresh_env.triedb, 2, DOMAIN_A, keccak(out_of_gas)
    ) == (2, 1)
    assert query_domain_transaction_location(
        fresh_env.triedb, 2, DOMAIN_A, keccak(emit_log)
    ) == (2, 3)
    accounts = dump_state(fresh_env.triedb, 2)["domains"][domain_key(DOMAIN_A)][
        "accounts"
    ]
    assert int(accounts["0x" + INNER_ADDR.hex()]["nonce"]) == 4
    assert "storage" not in accounts["0x" + storage_contract.hex()]


def test_empty_domain_output_does_not_disturb_valid_domain(
    fresh_env: FreshEnv,
):
    rejected_a = _inner(nonce=0, to=OUTER_ADDR, value=1)
    accepted_b = _inner(nonce=0, to=OUTER_ADDR, domain_id=DOMAIN_B)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(0, DOMAIN_A, rejected_a),
            _outer(1, DOMAIN_B, accepted_b),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A, DOMAIN_B])

    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0) is None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0) is None
    assert (
        query_domain_transaction_location(
            fresh_env.triedb, 2, DOMAIN_A, keccak(rejected_a)
        )
        is None
    )
    stored_b = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_B, 0)
    assert stored_b is not None and stored_b.encoded == accepted_b
    receipt_b = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, 0)
    assert receipt_b is not None and receipt_b.status == 1


def test_domain_block_gas_limit_is_enforced_by_the_hub(fresh_env: FreshEnv):
    """The hub sells at most DOMAIN_BLOCK_GAS_LIMIT gas per domain and L1 block, so
    a call that would exceed it reverts and nothing of it reaches the domain."""
    cap = 150_000_000
    first = _inner(nonce=0, to=OUTER_ADDR)
    second = _inner(nonce=1, to=OUTER_ADDR)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(0, DOMAIN_A, first, paid_gas=cap - 1_000_000),
            _outer(1, DOMAIN_A, second, paid_gas=1_000_001),
            _outer(2, DOMAIN_A, second, paid_gas=1_000_000),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    assert [r.status for r in query_receipts(fresh_env.triedb, 2, 3)] == [1, 0, 1]
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0).encoded == first
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1).encoded == second
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 2) is None
    assert _fees_collected(dump_state(fresh_env.triedb, 2)) == (4_000_000 * 2 + cap) * DOMAIN_GAS_PRICE


def test_reverted_l1_sequencing_call_is_not_executed(fresh_env: FreshEnv):
    """Sequencing derives from the hub's event, which a reverted call never emits."""
    inner = _inner(nonce=0, to=OUTER_ADDR)
    encrypted = encrypt_inner_transaction(DOMAIN_KEYS[DOMAIN_A], inner)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            # Pays the fee, but runs out of gas inside the hub.
            _outer_raw(0, DOMAIN_A, encrypted, l1_gas_limit=30_000),
            _outer_raw(1, DOMAIN_A, encrypted),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A])

    assert [r.status for r in query_receipts(fresh_env.triedb, 2, 2)] == [0, 1]
    stored = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert stored is not None and stored.encoded == inner
    assert query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 1) is None
    assert _fees_collected(dump_state(fresh_env.triedb, 2)) == (4_000_000 * 2 + 1_500_000) * DOMAIN_GAS_PRICE


def test_interleaved_domains_form_independent_blocks(fresh_env: FreshEnv):
    contract_a = _contract_address(INNER_ADDR, 0)
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(
                0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(INNER_SSTORE_RUNTIME))
            ),
            _outer(
                1,
                DOMAIN_B,
                _inner(
                    nonce=0,
                    to=None,
                    data=_init_code(INNER_SSTORE_RUNTIME),
                    domain_id=DOMAIN_B,
                ),
            ),
            _outer(2, DOMAIN_A, _inner(nonce=1, to=contract_a)),
        ],
    )
    _run(fresh_env, [block], [DOMAIN_A, DOMAIN_B])

    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 1) is not None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 2) is None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, 0) is not None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, 1) is None
    dump = dump_state(fresh_env.triedb, 2)
    accounts_a = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    accounts_b = dump["domains"][domain_key(DOMAIN_B)]["accounts"]
    assert int(accounts_a["0x" + INNER_ADDR.hex()]["nonce"]) == 2
    assert int(accounts_b["0x" + INNER_ADDR.hex()]["nonce"]) == 1
    assert "storage" in accounts_a["0x" + contract_a.hex()]
    assert "storage" not in accounts_b["0x" + contract_a.hex()]


def test_gasless_state_and_block_tables_survive_restart(fresh_env: FreshEnv):
    contract = _contract_address(INNER_ADDR, 0)
    deploy_inner = _inner(nonce=0, to=None, data=_init_code(INNER_SSTORE_RUNTIME))
    call_inner = _inner(nonce=1, to=contract)
    blocks = [
        BlockSpec(
            seqno=1,
            timestamp=1_000_000_001,
            txs=[_outer(0, DOMAIN_A, deploy_inner)],
        ),
        BlockSpec(
            seqno=2,
            timestamp=1_000_000_002,
            txs=[_outer(1, DOMAIN_A, call_inner)],
        ),
        BlockSpec(seqno=3, timestamp=1_000_000_003, txs=[]),
    ]
    build_ledger(fresh_env.ledger, _with_committed_parent(blocks))
    common = {
        "private_domain_keys": _key_files(fresh_env, (DOMAIN_A,)),
        "private_domain_spokes": {DOMAIN_A: ACCESS_SPOKE},
        "private_domain_sequencer": HUB,
    }
    first = run_monad(fresh_env.ledger, fresh_env.triedb, nblocks=2, **common)
    assert first.returncode == 0, first.stderr[-4000:]
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0).status == 1

    second = run_monad(fresh_env.ledger, fresh_env.triedb, nblocks=1, **common)
    assert second.returncode == 0, second.stderr[-4000:]
    assert query_domain_receipt(fresh_env.triedb, 3, DOMAIN_A, 0).status == 1
    assert query_domain_receipt(fresh_env.triedb, 3, DOMAIN_A, 1) is None
    dump = dump_state(fresh_env.triedb, 3)
    accounts = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    assert int(accounts["0x" + INNER_ADDR.hex()]["nonce"]) == 2
    assert accounts["0x" + contract.hex()]["storage"]["0x" + bytes(32).hex()] == (
        "0x" + INNER_ADDR.rjust(32, b"\x00").hex()
    )

    third = run_monad(fresh_env.ledger, fresh_env.triedb, nblocks=1, **common)
    assert third.returncode == 0, third.stderr[-4000:]
    assert query_domain_receipt(fresh_env.triedb, 4, DOMAIN_A, 0) is None
    assert query_domain_transaction(fresh_env.triedb, 4, DOMAIN_A, 0) is None
    assert query_domain_transaction_location(
        fresh_env.triedb, 4, DOMAIN_A, keccak(deploy_inner)
    ) == (2, 0)
    assert query_domain_transaction_location(
        fresh_env.triedb, 4, DOMAIN_A, keccak(call_inner)
    ) == (3, 0)
    resolved_deploy = query_domain_transaction_and_receipt_by_hash(
        fresh_env.triedb, 4, DOMAIN_A, keccak(deploy_inner)
    )
    resolved_call = query_domain_transaction_and_receipt_by_hash(
        fresh_env.triedb, 4, DOMAIN_A, keccak(call_inner)
    )
    assert resolved_deploy is not None
    assert resolved_deploy[0].encoded == deploy_inner
    assert resolved_deploy[1].status == 1
    assert resolved_call is not None
    assert resolved_call[0].encoded == call_inner
    assert resolved_call[1].status == 1
    dump = dump_state(fresh_env.triedb, 4)
    accounts = dump["domains"][domain_key(DOMAIN_A)]["accounts"]
    assert int(accounts["0x" + INNER_ADDR.hex()]["nonce"]) == 2
    assert accounts["0x" + contract.hex()]["storage"]["0x" + bytes(32).hex()] == (
        "0x" + INNER_ADDR.rjust(32, b"\x00").hex()
    )


def test_unassigned_domain_payload_is_ignored(fresh_env: FreshEnv):
    block = BlockSpec(
        seqno=1,
        timestamp=1_000_000_001,
        txs=[
            _outer(
                0, DOMAIN_A, _inner(nonce=0, to=None, data=_init_code(INNER_SSTORE_RUNTIME))
            ),
            _outer(
                1,
                DOMAIN_B,
                _inner(
                    nonce=0,
                    to=None,
                    data=_init_code(INNER_SSTORE_RUNTIME),
                    domain_id=DOMAIN_B,
                ),
            ),
        ],
    )
    build_ledger(fresh_env.ledger, _with_committed_parent([block]))
    result = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=2,
        private_domain_keys=_key_files(fresh_env, (DOMAIN_A,)),
        private_domain_spokes={DOMAIN_A: ACCESS_SPOKE},
        private_domain_sequencer=HUB,
    )
    assert result.returncode == 0, result.stderr[-4000:]
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0) is not None
    assert query_domain_receipt(fresh_env.triedb, 2, DOMAIN_B, 0) is None
    assert query_domain_transaction_sender(fresh_env.triedb, 2, DOMAIN_B, 0) is None


def test_staged_gasless_block_is_discarded_when_l1_execution_fails(
    fresh_env: FreshEnv,
):
    committed_parent = BlockSpec(
        seqno=1,
        timestamp=1_000_000_000,
        txs=_committed_parent_transactions(),
    )
    build_ledger(fresh_env.ledger, [committed_parent])
    checkpointed = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=1,
        private_domain_keys=_key_files(fresh_env, (DOMAIN_A,)),
        private_domain_spokes={DOMAIN_A: ACCESS_SPOKE},
        private_domain_sequencer=HUB,
    )
    assert checkpointed.returncode == 0, checkpointed.stderr[-4000:]

    inner = _inner(nonce=0, to=OUTER_ADDR)
    sequenced = _outer(0, DOMAIN_A, inner)
    invalid_l1 = (
        Tx(
            nonce=9,
            gas_limit=21_000,
            max_priority_fee_per_gas=0,
            max_fee_per_gas=0,
            to=OUTER_ADDR,
            value=0,
        ),
        OUTER_KEY,
    )
    failing_block = BlockSpec(
        seqno=2,
        timestamp=1_000_000_001,
        txs=[sequenced, invalid_l1],
    )
    build_ledger(fresh_env.ledger, [committed_parent, failing_block])
    failed = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=1,
        private_domain_keys=_key_files(fresh_env, (DOMAIN_A,)),
        private_domain_spokes={DOMAIN_A: ACCESS_SPOKE},
        private_domain_sequencer=HUB,
    )
    assert failed.returncode != 0

    # Replace the rejected block and resume from the committed parent. The same
    # inner nonce must still execute, proving staging did not leak domain
    # state or block-table entries into the database.
    valid_block = BlockSpec(
        seqno=2,
        timestamp=1_000_000_001,
        txs=[sequenced],
    )
    build_ledger(fresh_env.ledger, [committed_parent, valid_block])
    recovered = run_monad(
        fresh_env.ledger,
        fresh_env.triedb,
        nblocks=1,
        private_domain_keys=_key_files(fresh_env, (DOMAIN_A,)),
        private_domain_spokes={DOMAIN_A: ACCESS_SPOKE},
        private_domain_sequencer=HUB,
    )
    assert recovered.returncode == 0, recovered.stderr[-4000:]
    receipt = query_domain_receipt(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert receipt is not None and receipt.status == 1
    stored = query_domain_transaction(fresh_env.triedb, 2, DOMAIN_A, 0)
    assert stored is not None and stored.encoded == inner
    accounts = dump_state(fresh_env.triedb, 2)["domains"][domain_key(DOMAIN_A)][
        "accounts"
    ]
    assert int(accounts["0x" + INNER_ADDR.hex()]["nonce"]) == 1
