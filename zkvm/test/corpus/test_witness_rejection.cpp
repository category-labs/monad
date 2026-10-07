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

// Negative witnesses must make the guest reject, not merely produce different
// output. Run the guest as a subprocess to observe abort status without
// duplicating its input/output and allocator shims in gtest.

#include <zkvm/test/corpus/corpus_builder.hpp>
#include <zkvm/test/corpus/scenarios.hpp>
#include <zkvm/test/corpus/spoke_code.hpp>
#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <functional>
#include <string>
#include <vector>

using namespace monad;
using namespace monad::literals;

namespace
{
    constexpr auto KEY_A =
        0x0000000000000000000000000000000000000000000000000000000000000a11_bytes32;
    constexpr auto KEY_B =
        0x0000000000000000000000000000000000000000000000000000000000000b22_bytes32;
    constexpr auto OPERATOR_SK =
        0x00000000000000000000000000000000000000000000000000000000cafef00d_bytes32;
    constexpr auto SALT_SECRET =
        0x000000000000000000000000000000000000000000000000000000005a1700d5_bytes32;

    // Minimal RLP editing for malformed witnesses: replace envelope fields
    // that the normal encoder would only produce in valid form.

    struct Span
    {
        size_t begin;
        size_t end;
        size_t payload_begin;
        size_t payload_end;
    };

    Span rlp_item(byte_string_view const b, size_t const i)
    {
        MONAD_ASSERT(i < b.size());
        unsigned char const p = b[i];
        auto const fixed = [&](size_t const hdr, size_t const n) {
            return Span{i, i + hdr + n, i + hdr, i + hdr + n};
        };
        if (p < 0x80) {
            return Span{i, i + 1, i, i + 1};
        }
        if (p < 0xb8) {
            return fixed(1, p - 0x80u);
        }
        if (p < 0xc0) {
            size_t const k = p - 0xb7u;
            size_t n = 0;
            for (size_t j = 0; j < k; ++j) {
                n = (n << 8) | b[i + 1 + j];
            }
            return fixed(1 + k, n);
        }
        if (p < 0xf8) {
            return fixed(1, p - 0xc0u);
        }
        size_t const k = p - 0xf7u;
        size_t n = 0;
        for (size_t j = 0; j < k; ++j) {
            n = (n << 8) | b[i + 1 + j];
        }
        return fixed(1 + k, n);
    }

    std::vector<Span> rlp_children(byte_string_view const b, Span const &list)
    {
        std::vector<Span> out;
        size_t i = list.payload_begin;
        while (i < list.payload_end) {
            out.push_back(rlp_item(b, i));
            i = out.back().end;
        }
        return out;
    }

    byte_string rlp_list(byte_string_view const payload)
    {
        byte_string out;
        if (payload.size() < 56) {
            out.push_back(static_cast<unsigned char>(0xc0 + payload.size()));
        }
        else {
            byte_string be;
            for (size_t n = payload.size(); n != 0; n >>= 8) {
                be.insert(be.begin(), static_cast<unsigned char>(n & 0xff));
            }
            out.push_back(static_cast<unsigned char>(0xf7 + be.size()));
            out += be;
        }
        out += payload;
        return out;
    }

    /// Rebuild a witness with field `index` replaced. Every other field is
    /// copied verbatim, so the result differs only where it is meant to.
    byte_string replace_field(
        byte_string const &witness, size_t const index,
        byte_string_view const replacement)
    {
        byte_string_view const b{witness};
        auto const outer = rlp_item(b, 0);
        auto const fields = rlp_children(b, outer);
        MONAD_ASSERT(index < fields.size());
        byte_string inner;
        for (size_t i = 0; i < fields.size(); ++i) {
            if (i == index) {
                inner += replacement;
            }
            else {
                inner.append(
                    witness.begin() + static_cast<ptrdiff_t>(fields[i].begin),
                    witness.begin() + static_cast<ptrdiff_t>(fields[i].end));
            }
        }
        return rlp_list(inner);
    }

    /// The ancestor-header list (field [3]) with the entries at `drop` removed.
    byte_string
    drop_ancestors(byte_string const &witness, std::vector<size_t> const &drop)
    {
        byte_string_view const b{witness};
        auto const outer = rlp_item(b, 0);
        auto const fields = rlp_children(b, outer);
        auto const entries = rlp_children(b, fields[3]);
        byte_string kept;
        for (size_t i = 0; i < entries.size(); ++i) {
            if (std::find(drop.begin(), drop.end(), i) != drop.end()) {
                continue;
            }
            kept.append(
                witness.begin() + static_cast<ptrdiff_t>(entries[i].begin),
                witness.begin() + static_cast<ptrdiff_t>(entries[i].end));
        }
        return replace_field(witness, 3, rlp_list(kept));
    }

#ifdef MONAD_ZKVM_L2
    /// The block's own header, as it sits in field [0]. On the domain arm the
    /// ancestor run is 32-byte hashes, so appending a whole header to it makes
    /// an entry that is not one -- which is what that arm can still refuse.
    byte_string own_header(byte_string const &witness)
    {
        byte_string_view const b{witness};
        auto const outer = rlp_item(b, 0);
        auto const fields = rlp_children(b, outer);
        // [0] is the block RLP as a string; its payload is the block list,
        // whose first item is the header.
        Span const block_list = rlp_item(b, fields[0].payload_begin);
        auto const parts = rlp_children(b, block_list);
        byte_string header{
            witness.begin() + static_cast<ptrdiff_t>(parts[0].begin),
            witness.begin() + static_cast<ptrdiff_t>(parts[0].end)};
        // Field [3] holds each header wrapped as a string.
        byte_string out;
        if (header.size() < 56) {
            out.push_back(static_cast<unsigned char>(0x80 + header.size()));
        }
        else {
            byte_string be;
            for (size_t n = header.size(); n != 0; n >>= 8) {
                be.insert(be.begin(), static_cast<unsigned char>(n & 0xff));
            }
            out.push_back(static_cast<unsigned char>(0xb7 + be.size()));
            out += be;
        }
        out += header;
        return out;
    }

    /// The ancestor list with `extra` appended.
    byte_string
    append_ancestor(byte_string const &witness, byte_string_view const extra)
    {
        byte_string_view const b{witness};
        auto const outer = rlp_item(b, 0);
        auto const fields = rlp_children(b, outer);
        byte_string kept{
            witness.begin() + static_cast<ptrdiff_t>(fields[3].payload_begin),
            witness.begin() + static_cast<ptrdiff_t>(fields[3].payload_end)};
        kept += extra;
        return replace_field(witness, 3, rlp_list(kept));
    }
#endif

    size_t ancestor_count(byte_string const &witness)
    {
        byte_string_view const b{witness};
        auto const outer = rlp_item(b, 0);
        return rlp_children(b, rlp_children(b, outer)[3]).size();
    }

    // ── driving the guest ────────────────────────────────────────────────────

    std::filesystem::path runner()
    {
        return test_resource::build_dir / "zkvm" / "guest" /
               "monad-zkvm-x86-test-runner";
    }

    struct Outcome
    {
        int status;
        std::string output;
    };

    Outcome run_guest(byte_string const &witness, char const *const tag)
    {
        auto const dir = std::filesystem::temp_directory_path();
        auto const in = dir / (std::string{"reject-"} + tag + ".witness");
        auto const log = dir / (std::string{"reject-"} + tag + ".log");
        {
            std::ofstream f{in, std::ios::binary};
            f.write(
                reinterpret_cast<char const *>(witness.data()),
                static_cast<std::streamsize>(witness.size()));
        }
        // stderr merged in: the assertion text is what identifies WHICH check
        // fired, and a test that only sees a non-zero exit would pass for the
        // wrong reason.
        std::string const cmd = runner().string() + " --input " + in.string() +
                                " --output " + (dir / "reject.out").string() +
                                " > " + log.string() + " 2>&1";
        int const status = std::system(cmd.c_str());
        std::ifstream f{log};
        std::string const out{
            std::istreambuf_iterator<char>{f},
            std::istreambuf_iterator<char>{}};
        return Outcome{status, out};
    }

    /// A chain long enough to have a middle: the block under test needs at
    /// least three ancestors for a gap to be a gap rather than a shorter run.
    corpus::Emitted build_chain(unsigned const blocks)
    {
        corpus::CorpusBuilder b{
            [](State &s) {
                s.add_to_balance(
                    corpus::address_of(KEY_A), 1000000000000000000_u256);
            },
            OPERATOR_SK,
            SALT_SECRET};
        // Every ancestor: these blocks read no hash, and the runs the tests
        // below cut have to be longer than the parent alone.
        b.set_ancestors(corpus::Ancestors::All);
        corpus::Emitted last{};
        for (unsigned i = 0; i < blocks; ++i) {
            corpus::BlockSpec spec;
            Transaction tx{
                .max_fee_per_gas = 100,
                .gas_limit = corpus::TRANSFER_GAS,
                .value = 1,
                .to = corpus::address_of(KEY_B),
                .type = TransactionType::eip1559,
                .max_priority_fee_per_gas = 1};
            tx.sc.chain_id = 1;
            spec.txs.push_back(tx);
            spec.keys.push_back(KEY_A);
            last = b.add_block(std::move(spec));
        }
        return last;
    }
}

// The witness the tampering starts from has to be accepted, or a rejection
// below proves nothing about the tampering.
TEST(WitnessRejection, TheUntamperedWitnessIsAccepted)
{
    auto const e = build_chain(4);
    auto const r = run_guest(e.witness, "clean");
    EXPECT_EQ(r.status, 0) << r.output;
}

#ifdef MONAD_ZKVM_L2
// Reject an unbound blinding seed. This check protects confidentiality:
// transition commitments can remain sound even with predictable blinders.
TEST(WitnessRejection, AWitnessWhoseSaltSecretDoesNotMatchIsRefused)
{
    auto const e = build_chain(2);
    byte_string tampered = e.witness;
    tampered.back() ^= 1u;
    ASSERT_EQ(tampered.size(), e.witness.size());

    auto const r = run_guest(tampered, "salt");
    EXPECT_NE(r.status, 0) << "an unbound blinder was accepted";
    EXPECT_NE(r.output.find("L2_SALT_COMMITMENT"), std::string::npos)
        << r.output;
}
#endif

// Ethereum ancestors are headers: require contiguity and the parent as the
// last entry. A header at the current height violates the latter. Domains
// carry positional 32-byte hashes instead: malformed entry widths are
// rejected, but omissions shift the remaining heights undetected. See
// DECISIONS.md for this authentication gap.
#ifndef MONAD_ZKVM_L2
// Omitting the parent must fail: no remaining header would bind the witness
// trie to the expected pre-state.
TEST(WitnessRejection, AWitnessWithNoParentIsRefused)
{
    auto const e = build_chain(4);
    auto const n = ancestor_count(e.witness);
    ASSERT_GE(n, 2u);
    auto const tampered = drop_ancestors(e.witness, {n - 1});
    ASSERT_EQ(ancestor_count(tampered), n - 1);

    auto const r = run_guest(tampered, "no-parent");
    EXPECT_NE(r.status, 0) << "the bypass is open";
    EXPECT_NE(r.output.find("checked_pre_state_root"), std::string::npos)
        << r.output;
}

// Remove an interior ancestor to test contiguity while retaining the parent.
// Removing only the oldest would leave a valid shorter run.
TEST(WitnessRejection, AGapInTheAncestorRunIsRefused)
{
    auto const e = build_chain(4);
    auto const n = ancestor_count(e.witness);
    ASSERT_GE(n, 3u);
    auto const tampered = drop_ancestors(e.witness, {n - 2});

    auto const r = run_guest(tampered, "gap");
    EXPECT_NE(r.status, 0) << "a gap in the ancestor run was accepted";
    EXPECT_NE(r.output.find("prev_number + 1"), std::string::npos) << r.output;
}
#else
TEST(WitnessRejection, AnAncestorEntryThatIsNotAHashIsRefused)
{
    auto const e = build_chain(4);
    auto const n = ancestor_count(e.witness);
    // A whole header, which is not 32 bytes.
    auto const tampered = append_ancestor(e.witness, own_header(e.witness));
    ASSERT_EQ(ancestor_count(tampered), n + 1);

    auto const r = run_guest(tampered, "not-a-hash");
    EXPECT_NE(r.status, 0)
        << "an ancestor entry that is not a hash was accepted";
    EXPECT_NE(r.output.find("sizeof(monad::bytes32_t)"), std::string::npos)
        << r.output;
}
#endif

namespace
{
    constexpr auto HASH_READER =
        0x000000000000000000000000000000000000b10c_address;
    /// SSTORE(0, BLOCKHASH(NUMBER - 3)): one hash, read three blocks back.
    byte_string const READS_A_HASH =
        byte_string{0x60, 0x03, 0x43, 0x03, 0x40, 0x60, 0x00, 0x55, 0x00};

    corpus::BlockSpec one_call(Address const &to, uint64_t const gas)
    {
        corpus::BlockSpec spec;
        Transaction tx{
            .max_fee_per_gas = 100,
            .gas_limit = gas,
            .value = 1,
            .to = to,
            .type = TransactionType::eip1559,
            .max_priority_fee_per_gas = 1};
        tx.sc.chain_id = 1;
        spec.txs.push_back(tx);
        spec.keys.push_back(KEY_A);
        return spec;
    }

    /// Four transfers, then a block whose transaction reads the hash of the
    /// block three back, witnessed with Ancestors::Reached: its field [3] is
    /// that block to the parent and nothing older.
    corpus::Emitted build_reading_chain()
    {
        corpus::CorpusBuilder b{
            [](State &s) {
                s.add_to_balance(
                    corpus::address_of(KEY_A), 1000000000000000000_u256);
                s.create_contract(HASH_READER);
                s.set_code(HASH_READER, READS_A_HASH);
            },
            OPERATOR_SK,
            SALT_SECRET};
        b.set_ancestors(corpus::Ancestors::Reached);
        for (unsigned i = 0; i < 4; ++i) {
            b.add_block(
                one_call(corpus::address_of(KEY_B), corpus::TRANSFER_GAS));
        }
        auto e = b.add_block(one_call(HASH_READER, 100000));
        MONAD_ASSERT(e.receipts.at(0).status == 1);
        return e;
    }
}

// What makes Ancestors::Reached sound is the guest, not the generator: the
// run back to the oldest hash the block reads is all it needs...
TEST(WitnessRejection, TheRunTheBlockReadsIsAccepted)
{
    auto const e = build_reading_chain();
    ASSERT_EQ(ancestor_count(e.witness), 3u);

    auto const r = run_guest(e.witness, "reached");
    EXPECT_EQ(r.status, 0) << r.output;
}

// A contiguous run ending at the parent can still omit a required hash.
// WitnessBlockHashBuffer::get must reject that read, not return zero.
TEST(WitnessRejection, ARunShortOfAHashTheBlockReadsIsRefused)
{
    auto const e = build_reading_chain();
    auto const tampered = drop_ancestors(e.witness, {0});
    ASSERT_EQ(ancestor_count(tampered), 2u);

    auto const r = run_guest(tampered, "short-run");
    EXPECT_NE(r.status, 0) << "a hash outside the ancestor run was answered";
    EXPECT_NE(r.output.find("not in witness"), std::string::npos) << r.output;
}
