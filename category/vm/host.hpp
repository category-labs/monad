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
#include <category/vm/evm/traits.hpp>
#include <category/vm/evm/tx_context.hpp>
#include <category/vm/runtime/types.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <optional>
#include <span>

namespace monad::vm
{
#if defined(MONAD_ZKVM_ZISK)
    namespace runtime
    {
        struct SstoreStatus
        {
            AccessStatus access;
            StorageStatus storage;
        };
    }
#endif

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

#if defined(MONAD_ZKVM_ZISK)
        /// Warm the slot and return its previous access status.
        /// Read into value only if warm or can_pay_cold_access is true.
        /// The caller must charge cold-access gas before using value.
        virtual AccessStatus sload_into(
            Address const &address, bytes32_t const &key,
            bool can_pay_cold_access, bytes32_t &value) noexcept = 0;

        // Warm the slot, then write if it was warm or the cold access is
        // affordable.
        virtual runtime::SstoreStatus sstore_into(
            Address const &address, bytes32_t const &key,
            bytes32_t const &value, bool can_pay_cold_access) noexcept = 0;

        /// Read the EIP-7702 delegate directly from the stored code.
        virtual std::optional<Address>
        delegate_of(monad_address const &address) const noexcept = 0;
#endif

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

        std::optional<Address>
        resolve_delegation(monad_address const &addr) const
        {
#if defined(MONAD_ZKVM_ZISK)
            return delegate_of(addr);
#else
            // Read one extra byte to reject longer code.
            uint8_t code_buffer[evm::delegation_indicator_size + 1];
            size_t const size = copy_code(
                addr, 0, code_buffer, evm::delegation_indicator_size + 1);
            return evm::designation_of({code_buffer, size});
#endif
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

#if defined(MONAD_ZKVM_ZISK)
namespace monad::vm::runtime
{
    [[gnu::always_inline]] inline Host &host_of(Context const &ctx) noexcept
    {
        return *ctx.host;
    }

    // The witness uses StateHost<traits>. Defining these calls alongside the
    // concrete host lets the compiler inline its methods.
    template <Traits traits>
    AccessStatus guest_sload_into(
        Host &, Address const &, bytes32_t const &, bool, bytes32_t &) noexcept;

    template <Traits traits>
    SstoreStatus guest_sstore_into(
        Host &, Address const &, bytes32_t const &, bytes32_t const &,
        bool can_pay_cold_access) noexcept;

    template <Traits traits>
    AccessStatus guest_access_account(Host &, Address const &) noexcept;

    template <Traits traits>
    vm::Result guest_call(Host &, Message const &) noexcept;

    bytes32_t guest_get_transient_storage(
        Host const &, Address const &, bytes32_t const &) noexcept;

    void guest_set_transient_storage(
        Host &, Address const &, bytes32_t const &, bytes32_t const &) noexcept;

    TxContext const *guest_get_tx_context(Host const &) noexcept;

    size_t guest_get_code_size(Host const &, Address const &) noexcept;

    uint256_t guest_get_balance(Host const &, Address const &) noexcept;

    void guest_emit_log(
        Host &, Address const &, uint8_t const *, size_t, bytes32_t const[],
        size_t) noexcept;

    std::optional<Address>
    guest_delegate_of(Host const &, monad_address const &) noexcept;
}
#endif
