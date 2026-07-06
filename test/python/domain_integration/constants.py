"""Monad-devnet test constants and well-known Hardhat/Anvil dev keys.

The private keys below are the public Hardhat/Anvil mnemonic set (`test test test
test test test test test test test test junk`). They are widely documented and
not a security-sensitive secret; they exist here purely to sign transactions in
local integration tests that run against a throwaway devnet DB.
"""

from __future__ import annotations

from eth_utils import keccak

DEVNET_CHAIN_ID = 20143

# ABI function selector used by the external domain sequencing contract.
SELECTOR_SEQUENCE_TO_DOMAIN = keccak(b"sequenceToDomain(uint64,bytes)")[:4]

# First six Hardhat/Anvil dev accounts — address and corresponding private key.
# Addresses appear in MONAD_DEVNET_ALLOC (each with 1e38 wei balance).
DEV_ACCOUNTS: list[tuple[bytes, bytes]] = [
    (
        bytes.fromhex("f39Fd6e51aad88F6F4ce6aB8827279cffFb92266"),
        bytes.fromhex(
            "ac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"
        ),
    ),
    (
        bytes.fromhex("70997970C51812dc3A010C7d01b50e0d17dc79C8"),
        bytes.fromhex(
            "59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d"
        ),
    ),
    (
        bytes.fromhex("3C44CdDdB6a900fa2b585dd299e03d12FA4293BC"),
        bytes.fromhex(
            "5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a"
        ),
    ),
    (
        bytes.fromhex("90F79bf6EB2c4f870365E785982E1f101E93b906"),
        bytes.fromhex(
            "7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6"
        ),
    ),
    (
        bytes.fromhex("15d34AAf54267DB7D7c367839AAf71A00a2C6A65"),
        bytes.fromhex(
            "47e179ec197488593b187f80a00eb0da91f1b9d0b13f8733639f19c30a34926a"
        ),
    ),
    (
        bytes.fromhex("9965507D1a55bcC2695C58ba16FB37d819B0A4dc"),
        bytes.fromhex(
            "8b3a350cf5c34c9194ca85829a2df0ec3153be0318b5e2d3348e872092edffba"
        ),
    ),
]
