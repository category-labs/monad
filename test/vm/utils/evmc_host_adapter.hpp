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

#include <category/core/bytes.hpp>
#include <category/vm/evm/access_status.h>
#include <category/vm/evm/page_storage_status.h>
#include <category/vm/evm/storage_status.h>
#include <category/vm/host.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <vector>

namespace monad::vm::test
{
    // Exposes a vm::Host through evmc's C host interface, for evmc_vm
    // implementations such as the OCaml spec VM.
    class EvmcHostAdapter final : public evmc::Host
    {
        vm::Host &host_;

    public:
        explicit EvmcHostAdapter(vm::Host &host) noexcept
            : host_{host}
        {
        }

        vm::Host &host() const noexcept
        {
            return host_;
        }

        bool account_exists(evmc::address const &addr) const noexcept override
        {
            return host_.account_exists(addr);
        }

        evmc::bytes32 get_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            return host_.get_storage(addr, key);
        }

        evmc_storage_status set_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &value) noexcept override
        {
            return to_evmc_storage_status(host_.set_storage(addr, key, value));
        }

        evmc::uint256be
        get_balance(evmc::address const &addr) const noexcept override
        {
            return host_.get_balance(addr);
        }

        size_t get_code_size(evmc::address const &addr) const noexcept override
        {
            return host_.get_code_size(addr);
        }

        evmc::bytes32
        get_code_hash(evmc::address const &addr) const noexcept override
        {
            return host_.get_code_hash(addr);
        }

        size_t copy_code(
            evmc::address const &addr, size_t const code_offset,
            uint8_t *const buffer_data,
            size_t const buffer_size) const noexcept override
        {
            return host_.copy_code(addr, code_offset, buffer_data, buffer_size);
        }

        bool selfdestruct(
            evmc::address const &addr,
            evmc::address const &beneficiary) noexcept override
        {
            return host_.selfdestruct(addr, beneficiary);
        }

        evmc::Result call(evmc_message const &msg) noexcept override
        {
            return host_.call(msg);
        }

        evmc_tx_context const *get_tx_context() const noexcept override
        {
            return host_.get_tx_context();
        }

        evmc::bytes32
        get_block_hash(int64_t const block_number) const noexcept override
        {
            return host_.get_block_hash(block_number);
        }

        void emit_log(
            evmc::address const &addr, uint8_t const *const data,
            size_t const data_size, evmc::bytes32 const topics[],
            size_t const num_topics) noexcept override
        {
            std::vector<bytes32_t> const log_topics(
                topics, topics + num_topics);
            host_.emit_log(
                addr, data, data_size, log_topics.data(), log_topics.size());
        }

        evmc_access_status
        access_account(evmc::address const &addr) noexcept override
        {
            return to_evmc_access_status(host_.access_account(addr));
        }

        evmc_access_status access_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) noexcept override
        {
            return to_evmc_access_status(host_.access_storage(addr, key));
        }

        evmc::bytes32 get_transient_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            return host_.get_transient_storage(addr, key);
        }

        void set_transient_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &value) noexcept override
        {
            host_.set_transient_storage(addr, key, value);
        }

        evmc_page_storage_status update_page(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc_storage_status const status) noexcept override
        {
            return to_evmc_page_storage_status(
                host_.update_page(addr, key, from_evmc_storage_status(status)));
        }
    };
}
