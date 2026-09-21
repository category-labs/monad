// Copyright (C) 2026 Category Labs, Inc.
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

// See l2_cipher.hpp for the construction, its standing, and the rejection
// discipline.

#include <zkvm/guest/l2_cipher.hpp>

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/core/poseidon2.hpp>
#include <zkvm/guest/l2_sponge.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr std::size_t KEY_ELEMS = 4;
constexpr std::size_t TAG_ELEMS = 4;
/// A compressed point is 33 bytes, so five elements at seven bytes each.
constexpr std::size_t POINT_ELEMS = 5;

using ContextElems = std::array<std::uint64_t, L2_CONTEXT_ELEMS>;
using Key = std::array<std::uint64_t, KEY_ELEMS>;

// int.hpp's helpers: a memcpy and a bswap, so one unaligned access and one
// rev8 rather than eight single-byte accesses with a shift each.
void put_be64(unsigned char *const p, std::uint64_t const v)
{
    store_be(p, v);
}

std::uint32_t get_be32(unsigned char const *const p)
{
    return load_be_unsafe<std::uint32_t>(p);
}

/// The per-transaction half of A, serialized at fixed widths -- which is what
/// makes it injective without carrying its own lengths -- and then packed seven
/// bytes per element. The block-constant half is not here; it reaches the
/// sponge as its domain context, see L2CipherContext.
ContextElems context_elems(
    std::span<unsigned char const, 33> const r,
    std::span<unsigned char const, 16> const nonce, std::uint32_t const len)
{
    unsigned char buf[L2_CONTEXT_BYTES];
    unsigned char *p = buf;
    std::memcpy(p, r.data(), r.size());
    p += r.size();
    std::memcpy(p, nonce.data(), nonce.size());
    p += nonce.size();
    put_be64(p, len);
    p += 8;
    MONAD_ASSERT(p == buf + sizeof(buf));

    ContextElems out{};
    MONAD_ASSERT(l2_pack_bytes(buf, out) == out.size());
    return out;
}

/// K = H_KDF(P, A; 4). P enters compressed, so it is one unambiguous encoding
/// of a point and not a bare x-coordinate.
Key derive_key(
    L2Point const &shared, ContextElems const &a, bytes32_t const &constants)
{
    unsigned char sec1[33];
    l2_point_compress(shared, std::span<unsigned char, 33>{sec1});
    std::array<std::uint64_t, POINT_ELEMS> p_elems{};
    MONAD_ASSERT(l2_pack_bytes(sec1, p_elems) == p_elems.size());

    L2IoOp const pattern[] = {
        {false, static_cast<std::uint32_t>(POINT_ELEMS + L2_CONTEXT_ELEMS)},
        {true, KEY_ELEMS}};
    L2Sponge s{
        L2Domain::kdf,
        pattern,
        std::span<unsigned char const, 32>{constants.bytes, 32},
        L2EcdhPoseidon2::LABEL};
    s.absorb(p_elems);
    s.absorb(a);
    Key k{};
    s.squeeze(k);
    s.finish();
    return k;
}

/// Z = H_STREAM(K, A; l).
///
/// A zero-element message has no keystream, and asking for one is not a
/// degenerate case to paper over -- SAFE's pattern records the operations that
/// actually happen, and a squeeze of nothing is not one of them. The sponge
/// says so by rejecting a zero-length op.
///
/// This matters beyond an empty message being odd: len is a wire field, and
/// l2_leaf_size(0) is a well-formed 85-byte leaf. Without this arm a leaf
/// declaring len = 0 reaches the sponge and ABORTS THE GUEST -- a halt on
/// attacker-chosen bytes, where the design promises every bad leaf is a
/// deterministic rejection that consumes one queue entry. The tag still binds
/// len through A, so an empty message stays distinguishable from any other.
void derive_masks(
    Key const &k, ContextElems const &a, bytes32_t const &constants,
    std::span<std::uint64_t> const z)
{
    if (z.empty()) {
        return;
    }
    L2IoOp const pattern[] = {
        {false, static_cast<std::uint32_t>(KEY_ELEMS + L2_CONTEXT_ELEMS)},
        {true, static_cast<std::uint32_t>(z.size())}};
    L2Sponge s{
        L2Domain::stream,
        pattern,
        std::span<unsigned char const, 32>{constants.bytes, 32},
        L2EcdhPoseidon2::LABEL};
    s.absorb(k);
    s.absorb(a);
    s.squeeze(z);
    s.finish();
}

/// T = H_AUTH(K, A, C; 4). The whole ciphertext is absorbed, so the tag binds
/// the key, the context and every element -- accepting one ciphertext under two
/// keys would need a collision of this hash, not of an internal state.
Key compute_tag(
    Key const &k, ContextElems const &a, bytes32_t const &constants,
    std::span<std::uint64_t const> const c)
{
    L2IoOp const pattern[] = {
        {false,
         static_cast<std::uint32_t>(KEY_ELEMS + L2_CONTEXT_ELEMS + c.size())},
        {true, TAG_ELEMS}};
    L2Sponge s{
        L2Domain::auth,
        pattern,
        std::span<unsigned char const, 32>{constants.bytes, 32},
        L2EcdhPoseidon2::LABEL};
    s.absorb(k);
    s.absorb(a);
    s.absorb(c);
    Key t{};
    s.squeeze(t);
    s.finish();
    return t;
}

// Eight bytes an element and the target is little-endian, so the wire form IS
// the in-register form: one unaligned access apiece.
void put_elems_le(
    unsigned char *const p, std::span<std::uint64_t const> const e)
{
    for (std::size_t i = 0; i < e.size(); ++i) {
        store_le(p + i * 8, e[i]);
    }
}

void get_elems_le(
    std::span<std::uint64_t> const e, unsigned char const *const p)
{
    for (std::size_t i = 0; i < e.size(); ++i) {
        e[i] = load_le_unsafe<std::uint64_t>(p + i * 8);
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bytes32_t l2_constants_digest(L2CipherContext const &ctx)
{
    // Fixed widths, so injective without carrying lengths. 85 bytes.
    unsigned char buf[85];
    unsigned char *p = buf;
    put_be64(p, ctx.version);
    p += 8;
    put_be64(p, ctx.chain_id);
    p += 8;
    std::memcpy(p, ctx.contract.bytes, sizeof(ctx.contract.bytes));
    p += sizeof(ctx.contract.bytes);
    put_be64(p, ctx.namespace_id);
    p += 8;
    put_be64(p, ctx.epoch);
    p += 8;
    std::memcpy(p, ctx.operator_pk, sizeof(ctx.operator_pk));
    p += sizeof(ctx.operator_pk);
    MONAD_ASSERT(p == buf + sizeof(buf));

    bytes32_t out;
    monad_poseidon2_256(buf, sizeof(buf), out.bytes);
    return out;
}

bool l2_check_operator_key(L2CipherContext const &ctx, L2Scalar const &sk)
{
    auto const pk = l2_point_decompress(
        std::span<unsigned char const, 33>{ctx.operator_pk, 33});
    if (!pk.has_value()) {
        return false;
    }
    auto const derived = l2_ecdh(sk, SECP256K1_G);
    return derived.has_value() && *derived == *pk;
}

bool l2_decrypt_leaf(
    L2CipherContext const &ctx, L2Scalar const &sk,
    std::span<unsigned char const> const leaf,
    std::vector<unsigned char> &plain)
{
    // A zero digest means the caller never ran l2_constants_digest. Not a
    // claim that zero is unreachable as a hash -- a guard against the one way
    // to build a context that tags every leaf under the wrong constants.
    MONAD_ASSERT(ctx.constants_digest != bytes32_t{});
    if (leaf.size() < L2_LEAF_OVERHEAD) {
        return false;
    }
    std::uint32_t const len = get_be32(&leaf[L2_LEAF_LEN_OFFSET]);
    // The declared length and the leaf's own size have to agree exactly: a
    // leaf carrying more elements than its length accounts for would let two
    // different wire strings decrypt to the same plaintext.
    if (leaf.size() != l2_leaf_size(len)) {
        return false;
    }
    std::size_t const n = l2_elem_count(len);

    auto const r_bytes =
        std::span<unsigned char const, 33>{&leaf[L2_LEAF_R_OFFSET], 33};
    auto const nonce =
        std::span<unsigned char const, 16>{&leaf[L2_LEAF_NONCE_OFFSET], 16};

    // Decompression is the curve-membership check.
    auto const r_point = l2_point_decompress(r_bytes);
    if (!r_point.has_value()) {
        return false;
    }
    auto const shared = l2_ecdh(sk, *r_point);
    if (!shared.has_value()) {
        return false;
    }

    auto const a = context_elems(r_bytes, nonce, len);
    Key const k = derive_key(*shared, a, ctx.constants_digest);

    std::vector<std::uint64_t> c(n);
    get_elems_le(c, &leaf[L2_LEAF_C_OFFSET]);
    // Every ciphertext element must be a canonical field element. Not a
    // formality: a non-canonical one cannot be absorbed by the sponge without
    // going outside what the AIR can prove, so it is rejected here, before the
    // tag, rather than becoming an unprovable block.
    for (std::uint64_t const e : c) {
        if (e >= GOLDILOCKS_P) {
            return false;
        }
    }

    // Encrypt-then-MAC: the tag is verified in full, and only then is a mask
    // applied. The two steps are separate calls so the order cannot be
    // rearranged without it being obvious.
    Key const want = compute_tag(k, a, ctx.constants_digest, c);
    unsigned char tag_bytes[32];
    put_elems_le(tag_bytes, want);
    if (std::memcmp(tag_bytes, &leaf[L2_LEAF_C_OFFSET + 8 * n], 32) != 0) {
        return false;
    }

    std::vector<std::uint64_t> z(n);
    derive_masks(k, a, ctx.constants_digest, z);
    for (std::size_t i = 0; i < n; ++i) {
        c[i] = goldilocks_sub(c[i], z[i]);
    }

    plain.resize(len);
    // A whole-word store for every element but the last: 7i + 8 <= len holds
    // while i + 1 < n, and the eighth byte it writes belongs to element i + 1,
    // which the next iteration overwrites. Ascending order is therefore
    // load-bearing, and the last element falls back to bytes because a word
    // there would write past the plaintext.
    for (std::size_t i = 0; i + 1 < n; ++i) {
        store_le(plain.data() + i * 7, c[i]);
    }
    if (n != 0) {
        std::size_t const base = (n - 1) * 7;
        for (std::size_t b = 0; base + b < len; ++b) {
            plain[base + b] = static_cast<unsigned char>(c[n - 1] >> (8u * b));
        }
    }
    // The tail of the last element is padding, and the length that makes the
    // padding unambiguous is in A, so it is authenticated. Nothing is checked
    // about its value and nothing may be: a sender is free to have encrypted
    // whatever was there.
    return true;
}

std::optional<L2EcdhPoseidon2::Secret> L2EcdhPoseidon2::bind_secret(
    Context const &ctx, std::span<unsigned char const, 32> const bytes)
{
    L2Scalar const sk = l2_scalar_from_be(bytes);
    // Both halves, and in this order: a scalar out of range would not be a
    // valid multiplier for the check below, and the check is what ties the
    // witness's secret to the compiled operator key. Failing either means the
    // witness is malformed -- the caller halts, and no proof exists for it.
    if (!l2_scalar_is_valid(sk) || !l2_check_operator_key(ctx, sk)) {
        return std::nullopt;
    }
    return sk;
}

bool L2EcdhPoseidon2::decrypt(
    Context const &ctx, Secret const &secret,
    std::span<unsigned char const> const leaf,
    std::vector<unsigned char> &plain)
{
    return l2_decrypt_leaf(ctx, secret, leaf, plain);
}

bool l2_encrypt_leaf(
    L2CipherContext const &ctx, L2Scalar const &r,
    std::span<unsigned char const, 16> const nonce,
    std::span<unsigned char const> const plain,
    std::vector<unsigned char> &leaf)
{
    // A zero digest means the caller never ran l2_constants_digest. Not a
    // claim that zero is unreachable as a hash -- a guard against the one way
    // to build a context that tags every leaf under the wrong constants.
    MONAD_ASSERT(ctx.constants_digest != bytes32_t{});
    auto const pk = l2_point_decompress(
        std::span<unsigned char const, 33>{ctx.operator_pk, 33});
    if (!pk.has_value() || !l2_scalar_is_valid(r)) {
        return false;
    }
    auto const r_point = l2_ecdh(r, SECP256K1_G);
    auto const shared = l2_ecdh(r, *pk);
    if (!r_point.has_value() || !shared.has_value()) {
        return false;
    }

    auto const len = static_cast<std::uint32_t>(plain.size());
    MONAD_ASSERT(plain.size() == len);
    std::size_t const n = l2_elem_count(len);

    unsigned char r_bytes[33];
    l2_point_compress(*r_point, std::span<unsigned char, 33>{r_bytes});

    auto const a = context_elems(
        std::span<unsigned char const, 33>{r_bytes, 33}, nonce, len);
    Key const k = derive_key(*shared, a, ctx.constants_digest);

    std::vector<std::uint64_t> c(n);
    MONAD_ASSERT(l2_pack_bytes(plain, c) == n);
    std::vector<std::uint64_t> z(n);
    derive_masks(k, a, ctx.constants_digest, z);
    for (std::size_t i = 0; i < n; ++i) {
        c[i] = goldilocks_add(c[i], z[i]);
    }
    Key const t = compute_tag(k, a, ctx.constants_digest, c);

    leaf.assign(l2_leaf_size(len), 0);
    std::memcpy(&leaf[L2_LEAF_R_OFFSET], r_bytes, sizeof(r_bytes));
    std::memcpy(&leaf[L2_LEAF_NONCE_OFFSET], nonce.data(), nonce.size());
    unsigned char len_be[8];
    put_be64(len_be, len);
    std::memcpy(&leaf[L2_LEAF_LEN_OFFSET], len_be + 4, 4);
    put_elems_le(&leaf[L2_LEAF_C_OFFSET], c);
    put_elems_le(&leaf[L2_LEAF_C_OFFSET + 8 * n], t);
    return true;
}

MONAD_NAMESPACE_END
