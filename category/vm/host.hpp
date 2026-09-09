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

#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

#include <exception>
#include <type_traits>

namespace monad::vm
{
    class VM;

    class Host : public evmc::Host
    {
        friend class VM;

    public:
        /// The host interface this VM dispatches through, hiding
        /// `evmc::Host::get_interface`. See host_shim below for why.
        static evmc_host_interface const &get_interface() noexcept;

        struct PageStorageStatus
        {
            bool first_page_write;
            bool grew_state;
        };

        virtual PageStorageStatus update_page(
            evmc::address const &, evmc::bytes32 const &,
            evmc_storage_status) noexcept = 0;

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

namespace monad::vm::host_shim
{
    // `evmc::address` and `evmc_address` are the derived class and its base, with
    // no data member added, so they are pointer-interconvertible; same for
    // `evmc::bytes32` over `evmc_bytes32`. Casting the reference is therefore
    // free and names the same object, where the submodule's adapters convert and
    // pay a block copy -- two of them, because gcc materialises one temporary for
    // the conversion and another for the binding.
    [[gnu::always_inline]] inline evmc::address const &
    addr(evmc_address const *const a) noexcept
    {
        static_assert(sizeof(evmc::address) == sizeof(evmc_address));
        static_assert(std::is_standard_layout_v<evmc::address>);
        return reinterpret_cast<evmc::address const &>(*a);
    }

    [[gnu::always_inline]] inline evmc::bytes32 const &
    word(evmc_bytes32 const *const b) noexcept
    {
        static_assert(sizeof(evmc::bytes32) == sizeof(evmc_bytes32));
        static_assert(std::is_standard_layout_v<evmc::bytes32>);
        return reinterpret_cast<evmc::bytes32 const &>(*b);
    }

    [[gnu::always_inline]] inline Host *of(evmc_host_context *const h) noexcept
    {
        return evmc::Host::from_context<Host>(h);
    }

    inline bool
    account_exists(evmc_host_context *h, evmc_address const *a) noexcept
    {
        return of(h)->account_exists(addr(a));
    }

    inline evmc_bytes32 get_storage(
        evmc_host_context *h, evmc_address const *a,
        evmc_bytes32 const *k) noexcept
    {
        return of(h)->get_storage(addr(a), word(k));
    }

    inline evmc_storage_status set_storage(
        evmc_host_context *h, evmc_address const *a, evmc_bytes32 const *k,
        evmc_bytes32 const *v) noexcept
    {
        return of(h)->set_storage(addr(a), word(k), word(v));
    }

    inline evmc_uint256be
    get_balance(evmc_host_context *h, evmc_address const *a) noexcept
    {
        return of(h)->get_balance(addr(a));
    }

    inline size_t
    get_code_size(evmc_host_context *h, evmc_address const *a) noexcept
    {
        return of(h)->get_code_size(addr(a));
    }

    inline evmc_bytes32
    get_code_hash(evmc_host_context *h, evmc_address const *a) noexcept
    {
        return of(h)->get_code_hash(addr(a));
    }

    inline size_t copy_code(
        evmc_host_context *h, evmc_address const *a, size_t offset,
        uint8_t *buffer, size_t size) noexcept
    {
        return of(h)->copy_code(addr(a), offset, buffer, size);
    }

    inline bool selfdestruct(
        evmc_host_context *h, evmc_address const *a,
        evmc_address const *beneficiary) noexcept
    {
        return of(h)->selfdestruct(addr(a), addr(beneficiary));
    }

    inline void emit_log(
        evmc_host_context *h, evmc_address const *a, uint8_t const *data,
        size_t data_size, evmc_bytes32 const topics[],
        size_t num_topics) noexcept
    {
        of(h)->emit_log(
            addr(a), data, data_size,
            static_cast<evmc::bytes32 const *>(topics), num_topics);
    }

    inline evmc_access_status
    access_account(evmc_host_context *h, evmc_address const *a) noexcept
    {
        return of(h)->access_account(addr(a));
    }

    inline evmc_access_status access_storage(
        evmc_host_context *h, evmc_address const *a,
        evmc_bytes32 const *k) noexcept
    {
        return of(h)->access_storage(addr(a), word(k));
    }

    inline evmc_bytes32 get_transient_storage(
        evmc_host_context *h, evmc_address const *a,
        evmc_bytes32 const *k) noexcept
    {
        return of(h)->get_transient_storage(addr(a), word(k));
    }

    inline void set_transient_storage(
        evmc_host_context *h, evmc_address const *a, evmc_bytes32 const *k,
        evmc_bytes32 const *v) noexcept
    {
        of(h)->set_transient_storage(addr(a), word(k), word(v));
    }
}

namespace monad::vm
{
    // `call`, `get_tx_context` and `get_block_hash` stay the submodule's: their
    // parameters and returns are the C types already, so those three adapters
    // convert nothing and there is no copy to remove.
    inline evmc_host_interface const &Host::get_interface() noexcept
    {
        static constexpr evmc_host_interface interface = {
            ::monad::vm::host_shim::account_exists,
            ::monad::vm::host_shim::get_storage,
            ::monad::vm::host_shim::set_storage,
            ::monad::vm::host_shim::get_balance,
            ::monad::vm::host_shim::get_code_size,
            ::monad::vm::host_shim::get_code_hash,
            ::monad::vm::host_shim::copy_code,
            ::monad::vm::host_shim::selfdestruct,
            ::evmc::internal::call,
            ::evmc::internal::get_tx_context,
            ::evmc::internal::get_block_hash,
            ::monad::vm::host_shim::emit_log,
            ::monad::vm::host_shim::access_account,
            ::monad::vm::host_shim::access_storage,
            ::monad::vm::host_shim::get_transient_storage,
            ::monad::vm::host_shim::set_transient_storage,
        };
        return interface;
    }
}
