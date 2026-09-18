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

// Rewrites a plaintext witness into an L2 one, which is how the L2 guest gets
// an oracle without a single witness being produced from scratch.
//
// Nothing in this repository produces witnesses -- encode_execution_witness's
// only caller is its own test -- so the trick is not to produce one but to
// REWRITE one. Encrypting the leaves and recomputing the transactions root
// changes nothing that execution reads: execute_block_header and
// ExecuteTransaction touch prev_randao, beneficiary, timestamp, number,
// gas_limit and base_fee_per_gas, not transactions_root. The decrypted
// transactions are byte for byte the originals. Therefore:
//
//   the L2 run's post-state and pre-state roots must equal the plaintext
//   run's, exactly. Only the block hash differs, and it differs by
//   construction.
//
// BOTH RUNS GO THROUGH ziskemu, on two guest ELFs -- zkvm/README.md has the
// invocation. Not through a host executor, and that is not a convenience
// choice: an x86 build of the guest is a different program from the one that
// gets proved, because the Poseidon2 permutation is the native port rather
// than csrs 0x812 and the ECDH is libsecp256k1 rather than zisklib. Two host
// arms agreeing would say nothing about the arm we prove, and for the ECDH it
// would compare libsecp256k1 against itself -- the one comparison with no
// value, since the property wanted is that zisklib and libsecp256k1 agree.
//
// This tool is the piece that IS host-side, and legitimately: it only rewrites
// bytes, and it shares l2_cipher with the guest, so the keystream it produces
// is the keystream the guest derives by construction rather than by agreement.
//
// What the rewrite loses, and it is worth saying: the block hash and the
// transactions root no longer match canonical mainnet, because the block is
// fabricated. The post-state and pre-state roots keep their oracle, and they
// are the two that exercise execution.
//
// The operator key is a COMPILED constant, so the flow is: generate a keypair,
// configure the build with -DMONAD_ZKVM_L2_OPERATOR_PK_X and _ODD, then run
// this with the matching --sk. A mismatch is caught immediately rather than at
// the first leaf.

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <zkvm/guest/body_roots.hpp>
#include <zkvm/guest/l2_cipher.hpp>
#include <zkvm/guest/l2_config.hpp>
#include <zkvm/guest/l2_ecdh.hpp>

#include <array>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iterator>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace
{
    int fail(char const *const what)
    {
        std::fprintf(stderr, "l2-witness: %s\n", what);
        return 1;
    }

    std::optional<monad::byte_string> read_file(std::string const &path)
    {
        std::ifstream in{path, std::ios::binary};
        if (!in) {
            return std::nullopt;
        }
        return monad::byte_string{
            std::istreambuf_iterator<char>{in},
            std::istreambuf_iterator<char>{}};
    }

    std::optional<monad::byte_string> from_hex(std::string_view s)
    {
        if (s.starts_with("0x")) {
            s.remove_prefix(2);
        }
        if (s.size() % 2 != 0) {
            return std::nullopt;
        }
        monad::byte_string out;
        for (size_t i = 0; i < s.size(); i += 2) {
            auto const nib = [](char const c) -> int {
                if (c >= '0' && c <= '9') {
                    return c - '0';
                }
                if (c >= 'a' && c <= 'f') {
                    return c - 'a' + 10;
                }
                if (c >= 'A' && c <= 'F') {
                    return c - 'A' + 10;
                }
                return -1;
            };
            int const hi = nib(s[i]);
            int const lo = nib(s[i + 1]);
            if (hi < 0 || lo < 0) {
                return std::nullopt;
            }
            out.push_back(static_cast<unsigned char>((hi << 4) | lo));
        }
        return out;
    }

    /// An already-encoded RLP payload back into its items, because the parser
    /// hands back payloads and the encoder wants items.
    std::optional<std::vector<monad::byte_string>>
    split_items(monad::byte_string_view payload)
    {
        std::vector<monad::byte_string> out;
        while (!payload.empty()) {
            auto const item = monad::rlp::parse_string_metadata(payload);
            if (item.has_error()) {
                return std::nullopt;
            }
            out.emplace_back(item.value().begin(), item.value().end());
        }
        return out;
    }

    /// The RLP list of ciphertext strings, plus the ommers and withdrawals the
    /// original block carried, under the rewritten header.
    monad::byte_string rebuild_block(
        monad::BlockHeader const &header,
        std::vector<monad::byte_string> const &ciphertexts,
        monad::byte_string_view const tail)
    {
        monad::byte_string txs;
        for (auto const &ct : ciphertexts) {
            txs += monad::rlp::encode_string2(ct);
        }
        monad::byte_string body;
        body += monad::rlp::encode_block_header(header);
        body += monad::rlp::encode_list2(txs);
        // Everything after the transactions list is copied verbatim -- ommers
        // and, if the block had them, withdrawals. Re-encoding them would risk
        // a canonicalisation difference for no gain.
        body.append(tail.begin(), tail.end());
        return monad::rlp::encode_list2(body);
    }
}

int main(int const argc, char **const argv)
{
    std::string in_path;
    std::string out_path;
    std::string sk_hex;
    bool check = false;
    for (int i = 1; i < argc; ++i) {
        std::string_view const a{argv[i]};
        if (a == "--in" && i + 1 < argc) {
            in_path = argv[++i];
        }
        else if (a == "--out" && i + 1 < argc) {
            out_path = argv[++i];
        }
        else if (a == "--sk" && i + 1 < argc) {
            sk_hex = argv[++i];
        }
        else if (a == "--check") {
            check = true;
        }
        else {
            std::fprintf(
                stderr,
                "Usage: %s --in <witness> --out <witness> --sk <64 hex> "
                "[--check]\n",
                argv[0]);
            return 1;
        }
    }
    if (in_path.empty() || out_path.empty() || sk_hex.empty()) {
        return fail("--in, --out and --sk are all required");
    }

    // The differential's reference arm consumes the ORIGINAL witness, not a
    // rewritten one -- that asymmetry IS the experiment. A tool built
    // alongside that arm has nothing to do, and rewriting anyway would hand it
    // a seven-field witness it rejects with InputTooLong, several build and
    // framing steps from here. Said now instead.
    if constexpr (monad::l2_leaves_are_plaintext()) {
        return fail(
            "built with MONAD_ZKVM_L2_PLAINTEXT_LEAVES: that arm reads the "
            "witness as it stands, so there is nothing to rewrite. Build this "
            "tool with the subject arm's defines instead");
    }

    auto const sk_bytes = from_hex(sk_hex);
    if (!sk_bytes.has_value() || sk_bytes->size() != 32) {
        return fail("--sk must be 32 bytes of hex");
    }
    auto const sk = monad::l2_scalar_from_be(
        std::span<unsigned char const, 32>{sk_bytes->data(), 32});
    if (!monad::l2_scalar_is_valid(sk)) {
        return fail("--sk is not a valid secp256k1 scalar");
    }

    auto const input = read_file(in_path);
    if (!input.has_value()) {
        return fail("cannot read --in");
    }

    auto const witness = monad::parse_execution_witness(*input);
    if (witness.has_error()) {
        return fail("--in is not a six-field witness");
    }
    auto const &w = witness.value();

    // Split the block: the header, the transactions list, and the tail.
    monad::byte_string_view block_view = w.block_rlp;
    auto payload = monad::rlp::parse_list_metadata(block_view);
    if (payload.has_error() || !block_view.empty()) {
        return fail("malformed block rlp");
    }
    auto body = payload.value();
    auto header_r = monad::rlp::decode_block_header(body);
    if (header_r.has_error()) {
        return fail("malformed block header");
    }
    auto header = std::move(header_r).value();

    std::vector<monad::byte_string_view> leaves;
    {
        auto after_header = body;
        auto items = monad::rlp::parse_list_metadata(after_header);
        if (items.has_error()) {
            return fail("malformed transactions list");
        }
        auto list = items.value();
        while (!list.empty()) {
            auto const before = list;
            if (list[0] >= 0xc0) {
                // Legacy: the leaf is the list INCLUDING its header.
                auto const inner = monad::rlp::parse_list_metadata(list);
                if (inner.has_error()) {
                    return fail("malformed legacy transaction");
                }
                leaves.push_back(before.substr(0, before.size() - list.size()));
            }
            else {
                // Typed: the leaf is the unwrapped type || payload.
                auto const str = monad::rlp::parse_string_metadata(list);
                if (str.has_error()) {
                    return fail("malformed typed transaction");
                }
                leaves.push_back(str.value());
            }
        }
        body = after_header; // the tail: ommers and maybe withdrawals
    }

    // Refuse what the guest would refuse, rather than emitting a witness that
    // dies on the far side of a build and a framing step.
    //
    // Pre-Merge blocks go whatever the levers say. They carry ommers, which
    // nothing here accepts, and the block reward they carry is only inert
    // because BOTH arms gate apply_block_reward out -- resting a corpus on
    // that is resting it on a gate rather than on the block. difficulty is the
    // marker: the Merge repurposed the field, so a post-Merge header is zero.
    if (header.difficulty != 0) {
        return fail(
            "block is pre-Merge: it carries ommers, which the L2 rejects -- "
            "rewrite a Paris-or-later block instead");
    }

    if (!body.empty()) {
        monad::byte_string_view tail = body;
        auto const ommers = monad::rlp::decode_block_header_vector(tail);
        if (ommers.has_error() || !ommers.value().empty()) {
            return fail("block has ommers, which the L2 rejects");
        }
        // Withdrawals are what a Shanghai-or-later block always carries, and
        // the guest rejects them as unauthorised balance creation unless
        // MONAD_ZKVM_L2_ALLOW_L1_SHAPE is on -- which this tool is compiled
        // with or without alongside the guest, so the two always agree about
        // what is admissible.
        if constexpr (!monad::l2_allows_l1_shape()) {
            if (!tail.empty()) {
                auto const w = monad::rlp::decode_withdrawal_list(tail);
                if (w.has_error() || !w.value().empty()) {
                    return fail(
                        "block has withdrawals, which the L2 rejects as "
                        "unauthorised balance creation -- rewrite a block from "
                        "Paris up to Shanghai, or build with "
                        "-DMONAD_ZKVM_L2_ALLOW_L1_SHAPE=ON");
                }
            }
        }
    }

    auto ctx = monad::l2_cipher_context(header);
    if (!monad::l2_check_operator_key(ctx, sk)) {
        return fail(
            "--sk does not match the compiled MONAD_ZKVM_L2_OPERATOR_PK_X; "
            "configure the build with this key's public half");
    }

    // A nonce per leaf, derived from the index. Deterministic on purpose: this
    // is a corpus tool, and a rerun must produce the same bytes.
    std::vector<monad::byte_string> ciphertexts;
    for (size_t i = 0; i < leaves.size(); ++i) {
        std::array<unsigned char, 16> nonce{};
        for (size_t b = 0; b < 8; ++b) {
            nonce[b] = static_cast<unsigned char>(i >> (8u * b));
        }
        std::vector<unsigned char> leaf;
        if (!monad::l2_encrypt_leaf(
                ctx,
                sk,
                nonce,
                std::span<unsigned char const>{
                    leaves[i].data(), leaves[i].size()},
                leaf)) {
            return fail("encryption failed");
        }
        ciphertexts.emplace_back(leaf.begin(), leaf.end());
    }

    // The root moves to the ciphertexts. Nothing execution reads changes.
    header.transactions_root = monad::ordered_trie_root(ciphertexts);

    auto const codes = split_items(w.encoded_codes);
    auto const headers = split_items(w.encoded_headers);
    if (!codes.has_value() || !headers.has_value()) {
        return fail("malformed code or ancestor-header section");
    }
    // Fields [4] and [5] are parsed and then ignored by the guest -- they are
    // there for can_sender_dip_into_reserve, which is MonadTraits-only and not
    // on this path -- so they are not carried over. Said out loud because if
    // the guest ever starts reading them, this drops them silently.
    if (!w.encoded_parent_senders_and_authorities.empty() ||
        !w.encoded_grandparent_senders_and_authorities.empty()) {
        std::fprintf(
            stderr,
            "l2-witness: dropping the sender/authority sections, which the "
            "guest does not read\n");
    }

    auto const block_rlp = rebuild_block(header, ciphertexts, body);
    auto const out = monad::encode_execution_witness_l2(
        block_rlp, w.encoded_nodes, *codes, *headers, *sk_bytes);

    if (check) {
        for (size_t i = 0; i < ciphertexts.size(); ++i) {
            std::vector<unsigned char> plain;
            if (!monad::l2_decrypt_leaf(ctx, sk, ciphertexts[i], plain)) {
                return fail("--check: a leaf did not decrypt");
            }
            if (monad::byte_string_view{plain.data(), plain.size()} !=
                leaves[i]) {
                return fail("--check: a leaf did not round-trip");
            }
        }
        std::fprintf(
            stderr,
            "l2-witness: %zu leaves round-tripped\n",
            ciphertexts.size());
    }

    std::ofstream o{out_path, std::ios::binary};
    if (!o) {
        return fail("cannot write --out");
    }
    o.write(
        reinterpret_cast<char const *>(out.data()),
        static_cast<std::streamsize>(out.size()));
    return 0;
}
