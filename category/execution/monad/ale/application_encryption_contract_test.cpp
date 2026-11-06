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

#include <category/core/address.hpp>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/ale/application_encryption_contract.hpp>
#include <category/execution/monad/ale/application_encryption_error.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <cstddef>
#include <memory>
#include <utility>

#include <gtest/gtest.h>

using namespace monad;

struct ApplicationEncryptionContractTest : public ::testing::Test
{
    vm::VM vm;
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb trie_db{db};
    BlockState block_state{trie_db, vm};
    State state{block_state, Incarnation{0, 0}};
    NoopCallTracer call_tracer;
    ApplicationEncryptionContract contract{state, call_tracer};
};

TEST_F(ApplicationEncryptionContractTest, unseal_decodes_dynamic_arguments)
{
    for (auto const &[blob_size, ctx_size] : {
             std::pair{0uz, 0uz},
             std::pair{33uz, 1uz},
             std::pair{1uz, 33uz},
             std::pair{33uz, 65uz},
         }) {
        SCOPED_TRACE(blob_size);
        SCOPED_TRACE(ctx_size);
        AbiEncoder encoder;
        encoder.add_bytes(byte_string(blob_size, 0xAB));
        encoder.add_bytes(byte_string(ctx_size, 0xCD));
        auto const input = encoder.encode_final();

        auto const result = contract.precompile_unseal(input, Address{}, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(
            result.assume_error(), ApplicationEncryptionError::NotImplemented);
    }
}

TEST_F(ApplicationEncryptionContractTest, unseal_rejects_truncated_arguments)
{
    AbiEncoder encoder;
    encoder.add_bytes(byte_string(33, 0xAB));
    encoder.add_bytes(byte_string(65, 0xCD));
    auto const encoded = encoder.encode_final();

    for (size_t size = 0; size < encoded.size(); ++size) {
        SCOPED_TRACE(size);
        auto const input = byte_string_view{encoded}.substr(0, size);
        auto const result = contract.precompile_unseal(input, Address{}, {});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.assume_error(), AbiDecodeError::InputTooShort);
    }
}

TEST(ApplicationEncryptionAd, binary_context_spans_two_words)
{
    auto const app_ctx = from_hex(
                             "000102030405060708090a0b0c0d0e0f10111213141516171"
                             "8191a1b1c1d1e1f20")
                             .value();
    // Independently encoded from the ABI tuple layout in Python. Each literal
    // below is one word; the label excludes its terminating null byte.
    auto const expected =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000080"
            "0000000000000000000000000000000000000000000000000000510000004eaf"
            "0000000000000000000000000123456789abcdef0123456789abcdef01234567"
            "00000000000000000000000000000000000000000000000000000000000000c0"
            "0000000000000000000000000000000000000000000000000000000000000014"
            "6d6f6e61642d7365616c65642d626c6f622d7631000000000000000000000000"
            "0000000000000000000000000000000000000000000000000000000000000021"
            "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
            "2000000000000000000000000000000000000000000000000000000000000000")
            .value();

    EXPECT_EQ(
        sealed_blob_ad(
            0x510000004eaf,
            0x0123456789abcdef0123456789abcdef01234567_address,
            app_ctx),
        expected);
}

TEST(ApplicationEncryptionAd, empty_context)
{
    auto const expected =
        from_hex(
            "0000000000000000000000000000000000000000000000000000000000000080"
            "0000000000000000000000000000000000000000000000000000510000004eaf"
            "0000000000000000000000000123456789abcdef0123456789abcdef01234567"
            "00000000000000000000000000000000000000000000000000000000000000c0"
            "0000000000000000000000000000000000000000000000000000000000000014"
            "6d6f6e61642d7365616c65642d626c6f622d7631000000000000000000000000"
            "0000000000000000000000000000000000000000000000000000000000000000")
            .value();

    EXPECT_EQ(
        sealed_blob_ad(
            0x510000004eaf,
            0x0123456789abcdef0123456789abcdef01234567_address,
            {}),
        expected);
}
