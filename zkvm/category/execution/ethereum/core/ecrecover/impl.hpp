// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/crypto/keccak.h>
#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
    #include <category/execution/ethereum/core/signature_hash.hpp>
#endif

#include <c-interface-accelerators/zkvm_accelerators.h>

#include <cstdint>
#include <cstring>
#include <span>

#if defined(MONAD_ZKVM_ZISK)
// zkvm/zisk/src/ecrecover.rs: the scalars as little-endian words, the key
// written back as x || y in big-endian words.
extern "C" bool monad_zkvm_secp256k1_recover(
    uint64_t const *z, uint64_t const *r, uint64_t const *s, uint8_t recid,
    uint64_t *pubkey);
#endif

MONAD_NAMESPACE_BEGIN

[[gnu::always_inline]] inline bool recover_address(
    std::span<uint8_t, 20> const out, std::span<uint8_t const, 32> const msg,
    std::span<uint8_t const, 64> const sig, uint8_t const recid)
{
#if defined(MONAD_ZKVM_ZISK)
    // Words both ways: the Rust side is built without unaligned access, so a
    // byte pointer is read and written there a byte at a time.
    uint64_t const z[4] = {
        load_be_unsafe<uint64_t>(msg.data() + 24),
        load_be_unsafe<uint64_t>(msg.data() + 16),
        load_be_unsafe<uint64_t>(msg.data() + 8),
        load_be_unsafe<uint64_t>(msg.data())};
    uint64_t const r[4] = {
        load_be_unsafe<uint64_t>(sig.data() + 24),
        load_be_unsafe<uint64_t>(sig.data() + 16),
        load_be_unsafe<uint64_t>(sig.data() + 8),
        load_be_unsafe<uint64_t>(sig.data())};
    uint64_t const s[4] = {
        load_be_unsafe<uint64_t>(sig.data() + 56),
        load_be_unsafe<uint64_t>(sig.data() + 48),
        load_be_unsafe<uint64_t>(sig.data() + 40),
        load_be_unsafe<uint64_t>(sig.data() + 32)};
    uint64_t pubkey_words[8];
    if (!monad_zkvm_secp256k1_recover(z, r, s, recid, pubkey_words)) {
        return false;
    }
    auto const *const pubkey =
        reinterpret_cast<uint8_t const *>(pubkey_words);
#else
    auto const *msg_hash =
        reinterpret_cast<zkvm_secp256k1_hash const *>(msg.data());

    auto const *signature =
        reinterpret_cast<zkvm_secp256k1_signature const *>(sig.data());

    zkvm_secp256k1_pubkey pubkey_struct;

    if (zkvm_secp256k1_ecrecover(
            msg_hash, signature, recid, &pubkey_struct) != ZKVM_EOK) {
        return false;
    }
    auto const *const pubkey = pubkey_struct.data;
#endif

#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
    // The chain's address hash, signature_hash.hpp's.
    pubkey_address(std::span<uint8_t const, 64>{pubkey, 64}, out);
#else
    // Spell out the Keccak path to preserve default-build code generation.
    // Use the guest sponge and memo for recurring senders: measured at 36
    // steps per block versus 141 through zisklib.
    uint8_t key_hash[KECCAK256_SIZE];
    monad_zkvm_keccak256_fast(pubkey, 64, key_hash);

    std::memcpy(out.data(), key_hash + 12, out.size());
#endif

    return true;
}

MONAD_NAMESPACE_END
