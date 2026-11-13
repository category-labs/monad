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

// The StateInterface behaviour suite run against the guest State: the
// pre-state is a witness blob holding a canonical trie over the accounts
// and their slots, built with the production node writers, and each
// transaction is an epoch of the one State.

#include <zkvm/state/account_state.hpp>
#include <zkvm/state/state.hpp>
#include <zkvm/state/test_witness.hpp>

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/state3/state_interface_test.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/config.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_TEST_NAMESPACE_BEGIN

namespace
{
    using namespace monad::zkvm::test;

    struct SlotEntry
    {
        bytes32_t hash;
        bytes32_t value;
    };

    struct AccountEntry
    {
        bytes32_t hash;
        Account account;
        mpt::NodeId storage;
    };

    template <class Entry>
    void sort_by_hash(std::vector<Entry> &entries)
    {
        std::sort(
            entries.begin(), entries.end(), [](Entry const &x, Entry const &y) {
                return std::memcmp(
                           x.hash.bytes, y.hash.bytes, sizeof(x.hash.bytes)) <
                       0;
            });
    }

    // The canonical trie over `entries`, sorted by hash, from nibble `depth`
    // down; children are written before their parent since an id is an
    // offset. One entry is a leaf spelling the rest of its key; several that
    // share a prefix hang off an extension; otherwise a branch splits them.
    template <class Entry, class Leaf>
    mpt::NodeId build(
        byte_string &blob, std::span<Entry const> const entries,
        unsigned const depth, Leaf const &leaf)
    {
        if (entries.empty()) {
            return mpt::NULL_ID;
        }
        if (entries.size() == 1) {
            return leaf(
                blob,
                entries[0],
                zkvm::key_path(entries[0].hash).substr(depth));
        }
        auto const first = zkvm::key_path(entries.front().hash);
        auto const last = zkvm::key_path(entries.back().hash);
        unsigned shared = 0;
        while (depth + shared < first.nibble_size() &&
               first.get(depth + shared) == last.get(depth + shared)) {
            ++shared;
        }
        if (shared > 0) {
            auto const child = build(blob, entries, depth + shared, leaf);
            auto const id = here(blob);
            mpt::append_ext(blob, first.substr(depth, shared), child);
            return id;
        }
        std::array<mpt::NodeId, 16> children{};
        for (size_t i = 0; i < entries.size();) {
            unsigned const nibble = zkvm::key_path(entries[i].hash).get(depth);
            size_t j = i;
            while (j < entries.size() &&
                   zkvm::key_path(entries[j].hash).get(depth) == nibble) {
                ++j;
            }
            children[nibble] =
                build(blob, entries.subspan(i, j - i), depth + 1, leaf);
            i = j;
        }
        auto const id = here(blob);
        mpt::append_branch(blob, children);
        return id;
    }

    byte_string witness_blob(PreState const &pre)
    {
        auto blob = empty_blob();
        std::vector<AccountEntry> accounts;
        accounts.reserve(pre.accounts.size());
        for (auto const &a : pre.accounts) {
            std::vector<SlotEntry> slots;
            slots.reserve(a.storage.size());
            for (auto const &[key, value] : a.storage) {
                slots.push_back({to_bytes(keccak256(key.bytes)), value});
            }
            sort_by_hash(slots);
            auto const storage = build<SlotEntry>(
                blob,
                slots,
                0,
                [](byte_string &b,
                   SlotEntry const &e,
                   mpt::NibblesView const path) {
                    auto const id = here(b);
                    mpt::append_storage(b, path, e.value);
                    return id;
                });
            accounts.push_back(
                {to_bytes(keccak256(a.address.bytes)), a.account, storage});
        }
        sort_by_hash(accounts);
        auto const root = build<AccountEntry>(
            blob,
            accounts,
            0,
            [](byte_string &b,
               AccountEntry const &e,
               mpt::NibblesView const path) {
                auto const id = here(b);
                mpt::append_acct(b, e.storage, e.account, path);
                return id;
            });
        set_root(blob, root);
        return blob;
    }

    struct Guest
    {
        using State = zkvm::State;

        byte_string blob;
        vm::VM vm;
        std::optional<State> st;
        uint64_t tx{0};

        explicit Guest(PreState const &pre)
            : blob{witness_blob(pre)}
        {
            CodeTable table = codes();
            for (auto const &bytes : pre.codes) {
                table.try_emplace(
                    to_bytes(keccak256(bytes)),
                    varcode(std::vector<uint8_t>(bytes.begin(), bytes.end())));
            }
            st.emplace(
                mpt::OffsetTrie{blob}, std::move(table), vm, BLOCK, SEED);
            st->begin_transaction(tx);
        }

        State &state()
        {
            return *st;
        }

        void next_transaction()
        {
            st->take_logs();
            st->begin_transaction(++tx);
        }
    };

    using Shanghai = EvmTraits<EvmRevision::Shanghai>;
    using Cancun = EvmTraits<EvmRevision::Cancun>;
    using Amsterdam = EvmTraits<EvmRevision::Amsterdam>;

    using Params = ::testing::Types<
        Param<Guest, Shanghai>, Param<Guest, Cancun>, Param<Guest, Amsterdam>>;
}

INSTANTIATE_TYPED_TEST_SUITE_P(Guest, StateInterfaceTest, Params);

MONAD_TEST_NAMESPACE_END
