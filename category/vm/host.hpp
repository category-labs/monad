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
#include <category/core/throw.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/tx_context.hpp>
#include <category/vm/runtime/engine_timer.hpp>
#include <category/vm/runtime/types.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <optional>
#include <span>
#include <utility>

namespace monad::vm
{
    class VM;

    class Host
    {
        friend class VM;

    public:
        virtual ~Host() = default;

        bool account_exists(Address const &address) const
        {
            return guard<&Host::account_exists_impl>(address);
        }

        bytes32_t
        get_storage(Address const &address, bytes32_t const &key) const
        {
            return guard<&Host::get_storage_impl>(address, key);
        }

        StorageStatus set_storage(
            Address const &address, bytes32_t const &key,
            bytes32_t const &value)
        {
            return guard<&Host::set_storage_impl>(address, key, value);
        }

        uint256_t get_balance(Address const &address) const
        {
            return guard<&Host::get_balance_impl>(address);
        }

        size_t get_code_size(Address const &address) const
        {
            return guard<&Host::get_code_size_impl>(address);
        }

        bytes32_t get_code_hash(Address const &address) const
        {
            return guard<&Host::get_code_hash_impl>(address);
        }

        size_t copy_code(
            Address const &address, size_t const code_offset,
            uint8_t *const buffer_data, size_t const buffer_size) const
        {
            return guard<&Host::copy_code_impl>(
                address, code_offset, buffer_data, buffer_size);
        }

        bool selfdestruct(Address const &address, Address const &beneficiary)
        {
            return guard<&Host::selfdestruct_impl>(address, beneficiary);
        }

        Result call(Message const &msg)
        {
            return guard<&Host::call_impl>(msg);
        }

        virtual TxContext const *get_tx_context() const = 0;

        bytes32_t get_block_hash(int64_t const block_number) const
        {
            return guard<&Host::get_block_hash_impl>(block_number);
        }

        void emit_log(
            Address const &address, uint8_t const *const data,
            size_t const data_size, bytes32_t const topics[],
            size_t const num_topics)
        {
            guard<&Host::emit_log_impl>(
                address, data, data_size, topics, num_topics);
        }

        AccessStatus access_account(Address const &address)
        {
            return guard<&Host::access_account_impl>(address);
        }

        AccessStatus
        access_storage(Address const &address, bytes32_t const &key)
        {
            return guard<&Host::access_storage_impl>(address, key);
        }

        bytes32_t get_transient_storage(
            Address const &address, bytes32_t const &key) const
        {
            return guard<&Host::get_transient_storage_impl>(address, key);
        }

        void set_transient_storage(
            Address const &address, bytes32_t const &key,
            bytes32_t const &value)
        {
            guard<&Host::set_transient_storage_impl>(address, key, value);
        }

        PageStorageStatus update_page(
            Address const &address, bytes32_t const &key,
            StorageStatus const status)
        {
            return guard<&Host::update_page_impl>(address, key, status);
        }

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
        virtual bool account_exists_impl(Address const &) const = 0;

        virtual bytes32_t
        get_storage_impl(Address const &, bytes32_t const &key) const = 0;

        virtual StorageStatus set_storage_impl(
            Address const &, bytes32_t const &key, bytes32_t const &value) = 0;

        virtual uint256_t get_balance_impl(Address const &) const = 0;

        virtual size_t get_code_size_impl(Address const &) const = 0;

        virtual bytes32_t get_code_hash_impl(Address const &) const = 0;

        virtual size_t copy_code_impl(
            Address const &, size_t code_offset, uint8_t *buffer_data,
            size_t buffer_size) const = 0;

        virtual bool
        selfdestruct_impl(Address const &, Address const &beneficiary) = 0;

        virtual Result call_impl(Message const &) = 0;

        virtual bytes32_t get_block_hash_impl(int64_t block_number) const = 0;

        virtual void emit_log_impl(
            Address const &, uint8_t const *data, size_t data_size,
            bytes32_t const topics[], size_t num_topics) = 0;

        virtual AccessStatus access_account_impl(Address const &) = 0;

        virtual AccessStatus
        access_storage_impl(Address const &, bytes32_t const &key) = 0;

        virtual bytes32_t get_transient_storage_impl(
            Address const &, bytes32_t const &key) const = 0;

        virtual void set_transient_storage_impl(
            Address const &, bytes32_t const &key, bytes32_t const &value) = 0;

        virtual PageStorageStatus update_page_impl(
            Address const &, bytes32_t const &key, StorageStatus) = 0;

        /// Exceptions must not unwind through VM code, so they go through
        /// `stack_unwind` instead.
        template <auto impl, typename Self, typename... Args>
        [[gnu::always_inline]]
        auto guard(this Self &self, Args &&...args)
            -> decltype((self.*impl)(std::forward<Args>(args)...))
        {
            MONAD_TRY
            {
                auto const timer = self.time_host();
                return (self.*impl)(std::forward<Args>(args)...);
            }
            MONAD_CATCH(...)
            {
                self.active_exception_ = std::current_exception();
            }
            self.stack_unwind();
        }

        [[nodiscard, gnu::always_inline]]
        runtime::EngineTimer::Scope time_host() const noexcept
        {
            return {
                runtime_context_ ? &runtime_context_->engine_timer : nullptr,
                runtime::EngineTimer::Host};
        }

        /// Propagate a previously captured exception through the most recent
        /// VM stack frame(s). The VM will re-throw the exception after
        /// unwinding the stack. IMPORTANT: Do not call this from a `catch`
        /// block, because it does not return. This can otherwise cause memory
        /// leaks due to missing deallocation of the current active exception.
        /// IMPORTANT: Since `stack_unwind` never returns, make sure there are
        /// no stack objects with uninvoked destructor.
        [[noreturn]] void stack_unwind() const
        {
            MONAD_ASSERT(active_exception_);
            // rethrow exceptions when running outside of vm execution context
            // (i.e. when runtime_context_ is unset)
            if (runtime_context_ == nullptr) {
                auto e = active_exception_;
                active_exception_ = std::exception_ptr{};
                std::rethrow_exception(std::move(e));
            }

            runtime_context_->stack_unwind();
        }

        [[gnu::always_inline]]
        void rethrow_on_active_exception()
        {
            if (MONAD_UNLIKELY(active_exception_)) {
                auto e = active_exception_;
                active_exception_ = std::exception_ptr{};
                std::rethrow_exception(std::move(e));
            }
        }

        [[gnu::always_inline]]
        runtime::Context *
        set_runtime_context(runtime::Context *const ctx) noexcept
        {
            auto *const prev = runtime_context_;
            runtime_context_ = ctx;
            return prev;
        }

        runtime::Context *runtime_context_{nullptr};
        mutable std::exception_ptr active_exception_;
    };
}
