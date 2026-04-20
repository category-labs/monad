// Copyright (C) 2025 Category Labs, Inc.
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

#include "evmone_backend.hpp"

#include "account.hpp"
#include "block.hpp"
#include "hash_utils.hpp"
#include "host.hpp"
#include "state.hpp"
#include "test_state.hpp"
#include "transaction.hpp"

#include "fuzzer_view.hpp"

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <evmone/constants.hpp>

#include <intx/intx.hpp>

#include <algorithm>
#include <cstdint>
#include <limits>
#include <memory>
#include <span>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace evmone::state;

namespace monad::vm::fuzzing
{
    // -- Sorted view types ---------------------------------------------------

    /// Generic sorted view over an unordered_map. ConvertFn is a stateless
    /// callable that transforms (key, map_value) -> Entry.
    template <typename Entry, typename MapValue, auto ConvertFn>
    class EvmoneSortedMapView final : public SortedView<Entry>
    {
        std::vector<evmc::bytes32> keys_;
        std::unordered_map<evmc::bytes32, MapValue> const &map_;

        class CursorImpl final : public Cursor<Entry>
        {
            EvmoneSortedMapView const &view_;
            size_t index_ = 0;

        public:
            explicit CursorImpl(EvmoneSortedMapView const &v)
                : view_(v)
            {
            }

            bool at_end() const override
            {
                return index_ >= view_.keys_.size();
            }

            Entry current() const override
            {
                auto const &key = view_.keys_[index_];
                return ConvertFn(key, view_.map_.at(key));
            }

            void advance() override
            {
                ++index_;
            }
        };

    public:
        explicit EvmoneSortedMapView(
            std::unordered_map<evmc::bytes32, MapValue> const &map)
            : map_(map)
        {
            keys_.reserve(map_.size());
            for (auto const &[k, _] : map_) {
                keys_.push_back(k);
            }
            std::sort(keys_.begin(), keys_.end());
        }

        size_t size() const override
        {
            return keys_.size();
        }

        std::unique_ptr<Cursor<Entry>> cursor() const override
        {
            return std::make_unique<CursorImpl>(*this);
        }
    };

    static StorageEntry
    to_storage_entry(evmc::bytes32 const &key, StorageValue const &val)
    {
        return {key, val.current, val.original, val.access_status};
    }

    static TransientStorageEntry to_transient_storage_entry(
        evmc::bytes32 const &key, evmc::bytes32 const &val)
    {
        return {key, val};
    }

    class EvmoneSortedStateView final : public SortedStateView
    {
        std::vector<evmc::address> addrs_;
        std::unordered_map<evmc::address, Account> const &accounts_;

    public:
        explicit EvmoneSortedStateView(
            std::unordered_map<evmc::address, Account> const &accounts)
            : accounts_(accounts)
        {
            addrs_.reserve(accounts_.size());
            for (auto const &[addr, _] : accounts_) {
                addrs_.push_back(addr);
            }
            std::sort(addrs_.begin(), addrs_.end());
        }

        size_t size() const override
        {
            return addrs_.size();
        }

        std::unique_ptr<SortedStorageView>
        storage(Address const &addr) const override
        {
            return std::make_unique<EvmoneSortedMapView<
                StorageEntry,
                StorageValue,
                to_storage_entry>>(accounts_.at(addr).storage);
        }

        std::unique_ptr<SortedTransientStorageView>
        transient_storage(Address const &addr) const override
        {
            return std::make_unique<EvmoneSortedMapView<
                TransientStorageEntry,
                evmc::bytes32,
                to_transient_storage_entry>>(
                accounts_.at(addr).transient_storage);
        }

        std::unique_ptr<Cursor<AccountEntry>> cursor() const override;

    private:
        class CursorImpl final : public Cursor<AccountEntry>
        {
            EvmoneSortedStateView const &view_;
            size_t index_ = 0;

        public:
            explicit CursorImpl(EvmoneSortedStateView const &v)
                : view_(v)
            {
            }

            bool at_end() const override
            {
                return index_ >= view_.addrs_.size();
            }

            AccountEntry current() const override
            {
                auto const &addr = view_.addrs_[index_];
                auto const &acc = view_.accounts_.at(addr);
                return {addr, acc.nonce, acc.balance, acc.code_hash, acc.code};
            }

            void advance() override
            {
                ++index_;
            }
        };
    };

    std::unique_ptr<Cursor<AccountEntry>> EvmoneSortedStateView::cursor() const
    {
        return std::make_unique<CursorImpl>(*this);
    }

    // -- EvmoneBackend implementation ----------------------------------------

    evmone::test::TestState EvmoneBackend::make_initial_state(
        std::span<GenesisAccount const> const genesis)
    {
        auto init = evmone::test::TestState{};
        for (auto const &account : genesis) {
            init[account.addr] = {
                .balance = account.balance, .storage = {}, .code = {}};
        }
        return init;
    }

    EvmoneBackend::EvmoneBackend(
        evmc::VM vm, std::span<GenesisAccount const> const genesis)
        : vm_(std::move(vm))
        , initial_(make_initial_state(genesis))
        , state_(initial_)
    {
    }

    Address
    EvmoneBackend::deploy(Address const &from, std::span<uint8_t const> code)
    {
        auto const code_bytes = evmc::bytes{code.data(), code.size()};
        auto const create_address =
            compute_create_address(from, state_.get_or_insert(from).nonce++);
        MONAD_ASSERT(state_.find(create_address) == nullptr);

        state_.insert(
            create_address,
            Account{
                .nonce = 0,
                .balance = 0,
                .code_hash = evmone::keccak256(code_bytes),
                .storage = {},
                .transient_storage = {},
                .code = code_bytes});

        MONAD_ASSERT(state_.find(create_address) != nullptr);
        return create_address;
    }

    evmc::Result
    EvmoneBackend::execute(evmc_message const &msg, evmc_revision rev)
    {
        // Pre-transaction clean-up.
        for (auto &[addr, acc] : state_.get_modified_accounts()) {
            acc.transient_storage.clear();
            acc.access_status = EVMC_ACCESS_COLD;
            acc.just_created = false;
            for (auto &[key, val] : acc.storage) {
                val.access_status = EVMC_ACCESS_COLD;
                val.original = val.current;
            }
        }

        auto const block = BlockInfo{};
        auto const hashes = evmone::test::TestBlockHashes{};
        auto &sender_acc = state_.get_or_insert(msg.sender);
        auto tx = Transaction{};
        tx.gas_limit = block_gas_limit;
        tx.sender = msg.sender;
        tx.nonce = sender_acc.nonce;
        tx.to = msg.recipient;

        constexpr auto effective_gas_price = 10;

        ++sender_acc.nonce;
        sender_acc.balance -= block_gas_limit * effective_gas_price;

        Host host{rev, vm_, state_, block, hashes, tx};

        sender_acc.access_status = EVMC_ACCESS_WARM;
        if (tx.to.has_value()) {
            host.access_account(*tx.to);
        }

        auto result = host.call(msg);
        auto gas_used = block_gas_limit - result.gas_left;

        auto const max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
        auto const refund_limit = gas_used / max_refund_quotient;
        auto const refund = std::min(result.gas_refund, refund_limit);
        gas_used -= refund;

        sender_acc.balance +=
            (block_gas_limit - gas_used) * effective_gas_price;

        // Apply destructs.
        std::erase_if(
            state_.get_modified_accounts(),
            [](std::pair<evmc::address const, Account> const &p) noexcept {
                return p.second.destructed;
            });

        // Delete empty accounts.
        if (rev >= EVMC_SPURIOUS_DRAGON) {
            std::erase_if(
                state_.get_modified_accounts(),
                [](std::pair<evmc::address const, Account> const &p) noexcept {
                    auto const &acc = p.second;
                    return acc.erase_if_empty && acc.is_empty();
                });
        }

        return result;
    }

    uint64_t EvmoneBackend::checkpoint()
    {
        return state_.checkpoint();
    }

    void EvmoneBackend::rollback(uint64_t id)
    {
        state_.rollback(id);
    }

    byte_string EvmoneBackend::get_code(Address const &addr)
    {
        if (auto *found = state_.find(addr); found != nullptr) {
            return found->code;
        }
        return {};
    }

    void EvmoneBackend::ensure_exists(Address const &addr)
    {
        state_.get_or_insert(addr);
    }

    void EvmoneBackend::normalize()
    {
        for (auto &[addr, acc] : state_.get_modified_accounts()) {
            for (auto it = acc.storage.begin(); it != acc.storage.end();) {
                auto const &[k, v] = *it;
                if (v.current == evmc::bytes32{} &&
                    v.original == evmc::bytes32{} &&
                    v.access_status == EVMC_ACCESS_COLD) {
                    it = acc.storage.erase(it);
                }
                else {
                    ++it;
                }
            }
            for (auto it = acc.transient_storage.begin();
                 it != acc.transient_storage.end();) {
                auto const &[k, v] = *it;
                if (v == evmc::bytes32{}) {
                    it = acc.transient_storage.erase(it);
                }
                else {
                    ++it;
                }
            }
        }
    }

    std::unique_ptr<SortedStateView> EvmoneBackend::sorted_view() const
    {
        return std::make_unique<EvmoneSortedStateView>(
            state_.get_modified_accounts());
    }

    size_t EvmoneBackend::max_code_size() const
    {
        return evmone::MAX_CODE_SIZE;
    }
}
