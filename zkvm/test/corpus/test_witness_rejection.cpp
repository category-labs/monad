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

// Witnesses the guest must REFUSE.
//
// Every other test here proves the guest accepts what it should. These prove
// it rejects what it should, which is the half that rots unnoticed: an
// assertion nothing exercises is an assertion nobody knows is still there, and
// the ones below guard properties whose absence produces a valid-looking proof
// rather than a crash.
//
// They drive the real guest as a subprocess rather than linking it, for two
// reasons. The guest signals a bad witness by aborting, so the thing under
// test is a process exit; and linking ffi.cpp into a gtest binary would mean
// reproducing the whole x86 driver -- read_input, write_output, the allocator
// shim -- which is a second copy of a thing that already exists and would be
// what got tested instead.

#include <zkvm/test/corpus/corpus_builder.hpp>
#include <zkvm/test/corpus/scenarios.hpp>
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

    // ── a minimal RLP surgeon ────────────────────────────────────────────────
    // Enough to open the witness envelope, replace one field, and close it
    // again. The witness encoder cannot do this: it builds well-formed
    // witnesses, and these are deliberately not.

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

    /// The block's own header, as it sits in field [0]. Appending it to the
    /// ancestor list makes a run that is contiguous and correctly named and
    /// still wrong -- an ancestor is strictly older than the block.
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
        corpus::Emitted last{};
        for (unsigned i = 0; i < blocks; ++i) {
            corpus::BlockSpec spec;
            Transaction tx{
                .max_fee_per_gas = 100,
                .gas_limit = 21000,
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

// checked_pre_state_root. Without it a witness that simply omits the parent
// leaves NOTHING tying the trie the guest executes against to any header --
// the prover would supply a trie of its choosing and the run would be
// internally consistent. Omission, not corruption, is the bypass: every
// remaining ancestor is genuine.
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

// The contiguity check. A gap leaves the BLOCKHASH buffer keyed on numbers the
// headers declare about themselves, so every hash BLOCKHASH returns for an
// ancestor would be the prover's to choose. The parent stays in place, so
// checked_pre_state_root passes and contiguity is what has to catch this --
// which is why dropping the OLDEST entry instead would prove nothing: that
// just makes a shorter, valid run.
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

#ifdef MONAD_ZKVM_L2
// The blinder's binding, and the one rejection here that is not about
// soundness. An unbound blinder is perfectly sound -- the commitment chain
// forces a prover to reuse whatever it chose -- so a build without this check
// produces proofs that all verify and blocks that all chain, while the state
// is testable by anyone who can guess it. Nothing else would ever say so.
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

// An "ancestor" at the block's own height. The run stays contiguous and every
// header still names the one before it, so neither of the checks above fires
// -- which is what makes this worth its own case.
//
// Not a soundness hole, and the test says so rather than implying otherwise:
// the interpreter bounds BLOCKHASH below the current height before the buffer
// is read, so no hash from here is reachable. What the assertion buys is that
// the witness is named where it is wrong, instead of the run aborting later
// inside get() on a lookback that should have worked.
TEST(WitnessRejection, AnAncestorAtTheBlockHeightIsRefused)
{
    auto const e = build_chain(4);
    auto const n = ancestor_count(e.witness);
    auto const tampered = append_ancestor(e.witness, own_header(e.witness));
    ASSERT_EQ(ancestor_count(tampered), n + 1);

    auto const r = run_guest(tampered, "own-height");
    EXPECT_NE(r.status, 0) << "an ancestor at the current height was accepted";
    EXPECT_NE(r.output.find("number < block.header.number"), std::string::npos)
        << r.output;
}
