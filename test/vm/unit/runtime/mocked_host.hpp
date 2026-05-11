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

#pragma once

#include <category/core/int.hpp>
#include <category/vm/host.hpp>

#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <cstddef>
#include <cstdint>
#include <map>
#include <set>
#include <utility>

namespace monad::vm::test
{
    class MockedHost : public Host
    {
        evmc::MockedHost inner_;

        static constexpr size_t PAGE_KEY_SHIFT = 7;

        struct PageGrowth
        {
            int current_state_growth{0};
            int net_state_growth{0};
        };

        using PageKey = std::pair<evmc::address, evmc::bytes32>;

        std::set<PageKey> read_accessed_pages_;
        std::set<PageKey> write_accessed_pages_;
        std::map<PageKey, PageGrowth> growth_;
        PageStorageStatus last_write_page_status_{};

        static evmc::bytes32
        compute_page_key(evmc::bytes32 const &slot_key) noexcept
        {
            return store_be_as<evmc::bytes32>(
                load_be<uint256_t>(slot_key) >> PAGE_KEY_SHIFT);
        }

    public:
        decltype(inner_.accounts) &accounts = inner_.accounts;
        decltype(inner_.recorded_calls) &recorded_calls = inner_.recorded_calls;
        decltype(inner_.recorded_logs) &recorded_logs = inner_.recorded_logs;
        decltype(inner_.recorded_selfdestructs) &recorded_selfdestructs =
            inner_.recorded_selfdestructs;
        decltype(inner_.recorded_account_accesses) &recorded_account_accesses =
            inner_.recorded_account_accesses;
        decltype(inner_.recorded_blockhashes) &recorded_blockhashes =
            inner_.recorded_blockhashes;
        decltype(inner_.tx_context) &tx_context = inner_.tx_context;
        decltype(inner_.block_hash) &block_hash = inner_.block_hash;
        decltype(inner_.call_result) &call_result = inner_.call_result;

        bool account_exists(evmc::address const &addr) const noexcept override
        {
            return inner_.account_exists(addr);
        }

        evmc::bytes32 get_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            return inner_.get_storage(addr, key);
        }

        evmc_storage_status set_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &v_new) noexcept override
        {
            auto const v_current = inner_.get_storage(addr, key);
            auto const p = PageKey{addr, compute_page_key(key)};

            bool first_page_write = false;
            if (v_current != v_new) {
                auto const [it, inserted] = write_accessed_pages_.insert(p);
                if (inserted) {
                    first_page_write = true;
                    growth_[p] = PageGrowth{};
                }
            }

            auto const zero = evmc::bytes32{};
            if (v_current == zero && v_new != zero) {
                growth_[p].current_state_growth += 1;
            }
            else if (v_current != zero && v_new == zero) {
                growth_[p].current_state_growth -= 1;
            }

            bool grew_state = false;
            if (growth_[p].current_state_growth > growth_[p].net_state_growth) {
                growth_[p].net_state_growth = growth_[p].current_state_growth;
                grew_state = true;
            }

            last_write_page_status_ = {first_page_write, grew_state};

            return inner_.set_storage(addr, key, v_new);
        }

        evmc::uint256be
        get_balance(evmc::address const &addr) const noexcept override
        {
            return inner_.get_balance(addr);
        }

        size_t get_code_size(evmc::address const &addr) const noexcept override
        {
            return inner_.get_code_size(addr);
        }

        evmc::bytes32
        get_code_hash(evmc::address const &addr) const noexcept override
        {
            return inner_.get_code_hash(addr);
        }

        size_t copy_code(
            evmc::address const &addr, size_t code_offset, uint8_t *buffer_data,
            size_t buffer_size) const noexcept override
        {
            return inner_.copy_code(
                addr, code_offset, buffer_data, buffer_size);
        }

        bool selfdestruct(
            evmc::address const &addr,
            evmc::address const &beneficiary) noexcept override
        {
            return inner_.selfdestruct(addr, beneficiary);
        }

        evmc::Result call(evmc_message const &msg) noexcept override
        {
            return inner_.call(msg);
        }

        evmc_tx_context const *get_tx_context() const noexcept override
        {
            return inner_.get_tx_context();
        }

        evmc::bytes32
        get_block_hash(int64_t block_number) const noexcept override
        {
            return inner_.get_block_hash(block_number);
        }

        void emit_log(
            evmc::address const &addr, uint8_t const *data, size_t data_size,
            evmc::bytes32 const topics[], size_t topics_count) noexcept override
        {
            inner_.emit_log(addr, data, data_size, topics, topics_count);
        }

        evmc_access_status
        access_account(evmc::address const &addr) noexcept override
        {
            return inner_.access_account(addr);
        }

        evmc_access_status access_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) noexcept override
        {
            inner_.access_storage(addr, key);
            auto const p = PageKey{addr, compute_page_key(key)};
            auto const [it, inserted] = read_accessed_pages_.insert(p);
            return inserted ? EVMC_ACCESS_COLD : EVMC_ACCESS_WARM;
        }

        evmc::bytes32 get_transient_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            return inner_.get_transient_storage(addr, key);
        }

        void set_transient_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &value) noexcept override
        {
            inner_.set_transient_storage(addr, key, value);
        }

        PageStorageStatus update_page(
            evmc::address const &, evmc::bytes32 const &,
            evmc_storage_status) noexcept override
        {
            return last_write_page_status_;
        }
    };
}
