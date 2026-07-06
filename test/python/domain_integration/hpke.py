"""Independent RFC 9180 producer helpers for domain integration tests."""

from __future__ import annotations

from pathlib import Path
from typing import Mapping

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import ec
from hpke import (
    Suite__DHKEM_P256_HKDF_SHA256__HKDF_SHA256__AES_128_GCM as HpkeSuite,
)


HPKE_INFO = b"private-domain-hpke-rfc9180-v1"


def encrypt_inner_transaction(
    receiver_scalar: bytes,
    signed_transaction: bytes,
    *,
    frame_version: int = 1,
) -> bytes:
    """Return enc || ciphertext_and_tag for one Base-mode HPKE context."""
    if len(receiver_scalar) != 32:
        raise ValueError("receiver scalar must be 32 bytes")
    if not 0 <= frame_version <= 0xff:
        raise ValueError("frame version must fit one byte")
    receiver = ec.derive_private_key(
        int.from_bytes(receiver_scalar, "big"), ec.SECP256R1()
    )
    enc, ciphertext = HpkeSuite.seal(
        receiver.public_key(),
        HPKE_INFO,
        b"",
        bytes([frame_version]) + signed_transaction,
    )
    assert len(enc) == 65 and enc[0] == 0x04
    return enc + ciphertext


def write_private_key_files(
    directory: Path,
    keys: Mapping[int, bytes],
) -> dict[int, Path]:
    """Write unencrypted PKCS#8 PEM keys with owner-only permissions."""
    directory.mkdir(parents=True, exist_ok=True)
    paths: dict[int, Path] = {}
    for domain_id, scalar in keys.items():
        if len(scalar) != 32:
            raise ValueError("receiver scalar must be 32 bytes")
        key = ec.derive_private_key(
            int.from_bytes(scalar, "big"), ec.SECP256R1()
        )
        path = directory / f"domain-{domain_id}.pem"
        path.write_bytes(
            key.private_bytes(
                serialization.Encoding.PEM,
                serialization.PrivateFormat.PKCS8,
                serialization.NoEncryption(),
            )
        )
        path.chmod(0o600)
        paths[domain_id] = path
    return paths
