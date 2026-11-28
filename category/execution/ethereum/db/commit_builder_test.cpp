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
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/crypto/hash256.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/update.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::mpt;

namespace
{
    Address make_address(size_t const i)
    {
        Address a{};
        a.bytes[0] = static_cast<uint8_t>(i);
        a.bytes[1] = static_cast<uint8_t>(i >> 8);
        return a;
    }

    bytes32_t make_slot(size_t const account, size_t const i)
    {
        bytes32_t s{};
        s.bytes[0] = static_cast<uint8_t>(account);
        s.bytes[1] = static_cast<uint8_t>(i);
        s.bytes[31] = 1;
        return s;
    }

    size_t
    index_of(NibblesView const key, std::vector<monad_hash256> const &hashes)
    {
        for (size_t i = 0; i < hashes.size(); ++i) {
            if (key == NibblesView{hashes[i]}) {
                return i;
            }
        }
        return hashes.size();
    }

    void expect_keys_hashed(size_t const accounts, size_t const slots)
    {
        Account account;
        account.nonce = 1;
        bytes32_t value{};
        value.bytes[31] = 1;

        StateDeltas deltas;
        std::vector<monad_hash256> account_hashes;
        std::vector<std::vector<monad_hash256>> slot_hashes(accounts);
        for (size_t a = 0; a < accounts; ++a) {
            Address const addr = make_address(a);
            account_hashes.push_back(keccak256(addr.bytes));
            StateDelta delta{.account = {std::nullopt, account}};
            for (size_t s = 0; s < slots; ++s) {
                bytes32_t const slot = make_slot(a, s);
                slot_hashes[a].push_back(keccak256(slot.bytes));
                delta.storage.emplace(slot, StorageDelta{bytes32_t{}, value});
            }
            deltas.emplace(addr, std::move(delta));
        }

        CommitBuilder builder{1};
        builder.add_state_deltas(deltas);
        UpdateList const root = builder.build(NibblesView{});
        ASSERT_EQ(root.size(), 1);
        ASSERT_EQ(root.front().next.size(), 1);
        Update const &state = root.front().next.front();
        ASSERT_EQ(state.key, NibblesView{state_nibbles});

        size_t found_accounts = 0;
        for (Update const &account_update : state.next) {
            size_t const a = index_of(account_update.key, account_hashes);
            ASSERT_LT(a, accounts);
            ++found_accounts;
            size_t found_slots = 0;
            for (Update const &slot_update : account_update.next) {
                EXPECT_LT(index_of(slot_update.key, slot_hashes[a]), slots);
                ++found_slots;
            }
            EXPECT_EQ(found_slots, slots);
        }
        EXPECT_EQ(found_accounts, accounts);
    }
}

// The builder hashes state keys in batches of up to 64; these sizes put the
// key count on both sides of that boundary.
TEST(CommitBuilder, state_keys_are_keccak_of_addresses_and_slots)
{
    for (auto const [accounts, slots] : std::vector<std::pair<size_t, size_t>>{
             {1, 0}, {1, 62}, {1, 63}, {1, 64}, {2, 63}, {10, 14}, {3, 99}}) {
        SCOPED_TRACE(
            testing::Message()
            << accounts << " accounts x " << slots << " slots");
        expect_keys_hashed(accounts, slots);
    }
}
