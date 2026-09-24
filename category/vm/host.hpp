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
#include <category/vm/evm/access_status.h>
#include <category/vm/evm/page_storage_status.h>
#include <category/vm/evm/storage_status.h>
#include <category/vm/evm/tx_context.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <exception>

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

        virtual monad_storage_status set_storage(
            Address const &, bytes32_t const &key, bytes32_t const &value) = 0;

        virtual bytes32_t get_balance(Address const &) const = 0;

        virtual size_t get_code_size(Address const &) const = 0;

        virtual bytes32_t get_code_hash(Address const &) const = 0;

        virtual size_t copy_code(
            Address const &, size_t code_offset, uint8_t *buffer_data,
            size_t buffer_size) const = 0;

        virtual bool
        selfdestruct(Address const &, Address const &beneficiary) = 0;

        virtual evmc::Result call(evmc_message const &) = 0;

        virtual TxContext const *get_tx_context() const = 0;

        virtual bytes32_t get_block_hash(int64_t block_number) const = 0;

        virtual void emit_log(
            Address const &, uint8_t const *data, size_t data_size,
            bytes32_t const topics[], size_t num_topics) = 0;

        virtual monad_access_status access_account(Address const &) = 0;

        virtual monad_access_status
        access_storage(Address const &, bytes32_t const &key) = 0;

        virtual bytes32_t
        get_transient_storage(Address const &, bytes32_t const &key) const = 0;

        virtual void set_transient_storage(
            Address const &, bytes32_t const &key, bytes32_t const &value) = 0;

        virtual monad_page_storage_status update_page(
            Address const &, bytes32_t const &key, monad_storage_status) = 0;

        /// Capture `std::current_exception()`.
        /// IMPORTANT: Make sure to call this from inside a `catch` block.
        void capture_current_exception() const noexcept
        {
            active_exception_ = std::current_exception();
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

    private:
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
