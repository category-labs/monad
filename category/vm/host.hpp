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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/tx_context.hpp>
#include <category/vm/runtime/types.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

namespace monad::vm
{
    class VM;

    class Host
    {
        friend class VM;

    public:
        virtual ~Host() = default;

        virtual bool account_exists(Address const &) const = 0;

        virtual bytes32_t
        get_storage(Address const &, bytes32_t const &key) const = 0;

        virtual StorageStatus set_storage(
            Address const &, bytes32_t const &key, bytes32_t const &value) = 0;

        virtual uint256_t get_balance(Address const &) const = 0;

        virtual size_t get_code_size(Address const &) const = 0;

        virtual bytes32_t get_code_hash(Address const &) const = 0;

        virtual size_t copy_code(
            Address const &, size_t code_offset, uint8_t *buffer_data,
            size_t buffer_size) const = 0;

        virtual bool
        selfdestruct(Address const &, Address const &beneficiary) = 0;

        virtual Result call(Message const &) = 0;

        virtual TxContext const *get_tx_context() const = 0;

        virtual bytes32_t get_block_hash(int64_t block_number) const = 0;

        virtual void emit_log(
            Address const &, uint8_t const *data, size_t data_size,
            bytes32_t const topics[], size_t num_topics) = 0;

        virtual AccessStatus access_account(Address const &) = 0;

        virtual AccessStatus
        access_storage(Address const &, bytes32_t const &key) = 0;

        virtual bytes32_t
        get_transient_storage(Address const &, bytes32_t const &key) const = 0;

        virtual void set_transient_storage(
            Address const &, bytes32_t const &key, bytes32_t const &value) = 0;

        virtual PageStorageStatus
        update_page(Address const &, bytes32_t const &key, StorageStatus) = 0;

        std::optional<Address> resolve_delegation(Address const &addr) const
        {
            // Copy up to |code_size| bytes of the bytecode. Then test
            // whether the code begins with the prefix 0xEF0100, if so,
            // then drop these three bytes and interpret the remainder as
            // the delegate address.
            uint8_t code_buffer[evm::delegation_indicator_size + 1];
            size_t const actual_code_size = copy_code(
                addr, 0, code_buffer, evm::delegation_indicator_size + 1);

            std::span const code{code_buffer, actual_code_size};

            if (!evm::is_delegated(code)) {
                return std::nullopt;
            }

            // Copy the delegate address from the code buffer.
            Address designation;
            std::ranges::copy(
                code.subspan(
                    evm::delegation_indicator_prefix_bytes.size(),
                    sizeof(Address)),
                designation.bytes);
            return designation;
        }

    private:
        [[gnu::always_inline]]
        runtime::Context *
        set_runtime_context(runtime::Context *const ctx) noexcept
        {
            auto *const prev = runtime_context_;
            runtime_context_ = ctx;
            return prev;
        }

        runtime::Context *runtime_context_{nullptr};
    };
}
