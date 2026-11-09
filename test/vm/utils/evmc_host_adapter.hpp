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
#include <category/vm/host.hpp>

#include <test/vm/utils/evmc_bridge.hpp>
#include <test/vm/utils/evmc_result.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <vector>

namespace monad::vm::test
{
    // Exposes a vm::Host through evmc's C host interface, for the OCaml
    // spec VM.
    class EvmcHostAdapter final : public evmc::Host
    {
        vm::Host &host_;
        mutable evmc_tx_context tx_context_{};

    public:
        explicit EvmcHostAdapter(vm::Host &host) noexcept
            : host_{host}
        {
        }

        bool account_exists(evmc::address const &addr) const noexcept override
        {
            return host_.account_exists(from_evmc(addr));
        }

        evmc::bytes32 get_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            return to_evmc(host_.get_storage(from_evmc(addr), from_evmc(key)));
        }

        evmc_storage_status set_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &value) noexcept override
        {
            return to_evmc_storage_status(host_.set_storage(
                from_evmc(addr), from_evmc(key), from_evmc(value)));
        }

        evmc::uint256be
        get_balance(evmc::address const &addr) const noexcept override
        {
            return to_evmc(host_.get_balance(from_evmc(addr)));
        }

        size_t get_code_size(evmc::address const &addr) const noexcept override
        {
            return host_.get_code_size(from_evmc(addr));
        }

        evmc::bytes32
        get_code_hash(evmc::address const &addr) const noexcept override
        {
            return to_evmc(host_.get_code_hash(from_evmc(addr)));
        }

        size_t copy_code(
            evmc::address const &addr, size_t const code_offset,
            uint8_t *const buffer_data,
            size_t const buffer_size) const noexcept override
        {
            return host_.copy_code(
                from_evmc(addr), code_offset, buffer_data, buffer_size);
        }

        bool selfdestruct(
            evmc::address const &addr,
            evmc::address const &beneficiary) noexcept override
        {
            return host_.selfdestruct(from_evmc(addr), from_evmc(beneficiary));
        }

        evmc::Result call(evmc_message const &msg) noexcept override
        {
            return to_evmc_result(host_.call(from_evmc(msg)));
        }

        evmc_tx_context const *get_tx_context() const noexcept override
        {
            tx_context_ = to_evmc(*host_.get_tx_context());
            return &tx_context_;
        }

        evmc::bytes32
        get_block_hash(int64_t const block_number) const noexcept override
        {
            return to_evmc(host_.get_block_hash(block_number));
        }

        void emit_log(
            evmc::address const &addr, uint8_t const *const data,
            size_t const data_size, evmc::bytes32 const topics[],
            size_t const num_topics) noexcept override
        {
            std::vector<bytes32_t> log_topics;
            log_topics.reserve(num_topics);
            for (size_t i = 0; i < num_topics; ++i) {
                log_topics.push_back(from_evmc(topics[i]));
            }
            host_.emit_log(
                from_evmc(addr),
                data,
                data_size,
                log_topics.data(),
                log_topics.size());
        }

        evmc_access_status
        access_account(evmc::address const &addr) noexcept override
        {
            return to_evmc_access_status(host_.access_account(from_evmc(addr)));
        }

        evmc_access_status access_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) noexcept override
        {
            return to_evmc_access_status(
                host_.access_storage(from_evmc(addr), from_evmc(key)));
        }

        evmc::bytes32 get_transient_storage(
            evmc::address const &addr,
            evmc::bytes32 const &key) const noexcept override
        {
            return to_evmc(
                host_.get_transient_storage(from_evmc(addr), from_evmc(key)));
        }

        void set_transient_storage(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc::bytes32 const &value) noexcept override
        {
            host_.set_transient_storage(
                from_evmc(addr), from_evmc(key), from_evmc(value));
        }

        evmc_page_storage_status update_page(
            evmc::address const &addr, evmc::bytes32 const &key,
            evmc_storage_status const status) noexcept override
        {
            return to_evmc_page_storage_status(host_.update_page(
                from_evmc(addr),
                from_evmc(key),
                from_evmc_storage_status(status)));
        }
    };
}
