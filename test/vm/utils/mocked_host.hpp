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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/vm/host.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <map>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

namespace monad::vm::test
{
    struct StorageValue
    {
        bytes32_t current;
        bytes32_t original;
    };

    struct MockedAccount
    {
        byte_string code;
        bytes32_t codehash;
        bytes32_t balance;
        std::unordered_map<bytes32_t, StorageValue> storage;
        std::unordered_map<bytes32_t, bytes32_t> transient_storage;

        void set_balance(uint64_t const x) noexcept
        {
            balance = bytes32_t{x};
        }
    };

    struct LogRecord
    {
        Address creator;
        byte_string data;
        std::vector<bytes32_t> topics;
    };

    class MockedHost : public Host
    {
        struct PageGrowth
        {
            int current_state_growth{0};
            int net_state_growth{0};
        };

        using PageKey = std::pair<Address, bytes32_t>;

        std::set<PageKey> read_accessed_pages_;
        std::set<PageKey> write_accessed_pages_;
        std::map<PageKey, PageGrowth> growth_;
        evmc_page_storage_status last_write_page_status_{};

        void record_account_access(Address const &addr) const noexcept
        {
            recorded_account_accesses.emplace_back(addr);
        }

        static evmc_storage_status storage_status(
            bytes32_t const &original, bytes32_t const &current,
            bytes32_t const &value) noexcept
        {
            auto const zero = bytes32_t{};
            if (current == value) {
                return EVMC_STORAGE_ASSIGNED;
            }
            if (original == current) {
                if (original == zero) {
                    return EVMC_STORAGE_ADDED;
                }
                return value == zero ? EVMC_STORAGE_DELETED
                                     : EVMC_STORAGE_MODIFIED;
            }
            if (original != zero) {
                if (current == zero) {
                    return original == value ? EVMC_STORAGE_DELETED_RESTORED
                                             : EVMC_STORAGE_DELETED_ADDED;
                }
                if (value == zero) {
                    return EVMC_STORAGE_MODIFIED_DELETED;
                }
            }
            if (original == value) {
                return original == zero ? EVMC_STORAGE_ADDED_DELETED
                                        : EVMC_STORAGE_MODIFIED_RESTORED;
            }
            return EVMC_STORAGE_ASSIGNED;
        }

    public:
        std::unordered_map<Address, MockedAccount> accounts;
        evmc_tx_context tx_context{};
        bytes32_t block_hash;
        evmc_result call_result{};
        mutable std::vector<int64_t> recorded_blockhashes;
        mutable std::vector<Address> recorded_account_accesses;
        // Pointer fields are nulled on record; only scalars outlive the call.
        std::vector<evmc_message> recorded_calls;
        std::vector<LogRecord> recorded_logs;
        std::unordered_map<Address, std::vector<Address>>
            recorded_selfdestructs;

        bool account_exists(evmc::address const &addr) const noexcept override
        {
            record_account_access(addr);
            return accounts.contains(addr);
        }

        evmc::bytes32 get_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            record_account_access(addr);
            auto const account = accounts.find(addr);
            if (account == accounts.end()) {
                return {};
            }
            auto const slot = account->second.storage.find(key);
            if (slot == account->second.storage.end()) {
                return {};
            }
            return slot->second.current;
        }

        evmc_storage_status set_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &value) noexcept override
        {
            record_account_access(addr);
            auto &slot = accounts[addr].storage[key];
            auto const v_current = slot.current;
            auto const v_new = bytes32_t{value};
            auto const p = PageKey{addr, compute_page_key(key)};

            bool first_page_write = false;
            if (v_current != v_new) {
                auto const [it, inserted] = write_accessed_pages_.insert(p);
                if (inserted) {
                    first_page_write = true;
                    growth_[p] = PageGrowth{};
                }
            }

            auto const zero = bytes32_t{};
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

            auto const status = storage_status(slot.original, v_current, v_new);
            slot.current = v_new;
            return status;
        }

        evmc::uint256be
        get_balance(evmc::address const &addr) const noexcept override
        {
            record_account_access(addr);
            auto const account = accounts.find(addr);
            return account == accounts.end()
                       ? evmc::uint256be{}
                       : evmc::uint256be{account->second.balance};
        }

        size_t get_code_size(evmc::address const &addr) const noexcept override
        {
            record_account_access(addr);
            auto const account = accounts.find(addr);
            return account == accounts.end() ? 0 : account->second.code.size();
        }

        evmc::bytes32
        get_code_hash(evmc::address const &addr) const noexcept override
        {
            record_account_access(addr);
            auto const account = accounts.find(addr);
            return account == accounts.end()
                       ? evmc::bytes32{}
                       : evmc::bytes32{account->second.codehash};
        }

        size_t copy_code(
            evmc::address const &addr, size_t const code_offset,
            uint8_t *const buffer_data,
            size_t const buffer_size) const noexcept override
        {
            record_account_access(addr);
            auto const account = accounts.find(addr);
            if (account == accounts.end()) {
                return 0;
            }
            auto const &code = account->second.code;
            if (code_offset >= code.size()) {
                return 0;
            }
            auto const n = std::min(buffer_size, code.size() - code_offset);
            std::copy_n(code.data() + code_offset, n, buffer_data);
            return n;
        }

        bool selfdestruct(
            evmc::address const &addr,
            evmc::address const &beneficiary) noexcept override
        {
            record_account_access(addr);
            auto &beneficiaries = recorded_selfdestructs[addr];
            beneficiaries.emplace_back(beneficiary);
            return beneficiaries.size() == 1;
        }

        evmc::Result call(evmc_message const &msg) noexcept override
        {
            record_account_access(msg.recipient);
            auto &rec = recorded_calls.emplace_back(msg);
            rec.input_data = nullptr;
            rec.input_size = 0;
            rec.memory_handle = nullptr;
            rec.memory = nullptr;
            rec.memory_capacity = 0;
            return evmc::Result{call_result};
        }

        evmc_tx_context const *get_tx_context() const noexcept override
        {
            return &tx_context;
        }

        evmc::bytes32
        get_block_hash(int64_t const block_number) const noexcept override
        {
            recorded_blockhashes.emplace_back(block_number);
            return block_hash;
        }

        void emit_log(
            evmc::address const &addr, uint8_t const *const data,
            size_t const data_size, evmc::bytes32 const topics[],
            size_t const topics_count) noexcept override
        {
            recorded_logs.push_back(
                {addr, {data, data_size}, {topics, topics + topics_count}});
        }

        evmc_access_status
        access_account(evmc::address const &addr) noexcept override
        {
            auto const a = Address{addr};
            auto const already_accessed =
                std::ranges::find(recorded_account_accesses, a) !=
                recorded_account_accesses.end();
            record_account_access(a);
            return already_accessed ? EVMC_ACCESS_WARM : EVMC_ACCESS_COLD;
        }

        evmc_access_status access_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) noexcept override
        {
            auto const p = PageKey{addr, compute_page_key(key)};
            auto const [it, inserted] = read_accessed_pages_.insert(p);
            return inserted ? EVMC_ACCESS_COLD : EVMC_ACCESS_WARM;
        }

        evmc::bytes32 get_transient_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            record_account_access(addr);
            auto const account = accounts.find(addr);
            if (account == accounts.end()) {
                return {};
            }
            auto const slot = account->second.transient_storage.find(key);
            if (slot == account->second.transient_storage.end()) {
                return {};
            }
            return slot->second;
        }

        void set_transient_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &value) noexcept override
        {
            record_account_access(addr);
            accounts[addr].transient_storage[key] = value;
        }

        evmc_page_storage_status update_page(
            evmc::address const &, evmc::bytes32 const &,
            evmc_storage_status) noexcept override
        {
            return last_write_page_status_;
        }
    };
}
