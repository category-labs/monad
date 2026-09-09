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

#include <chrono>
#include <cstdint>
#include <exception>

namespace monad::vm
{
    class VM;

    class Host : public evmc::Host
    {
        friend class VM;

    public:
        struct PageStorageStatus
        {
            bool first_page_write;
            bool grew_state;
        };

        virtual PageStorageStatus update_page(
            evmc::address const &, evmc::bytes32 const &,
            evmc_storage_status) noexcept = 0;

        /// Install an absolute execution deadline; every frame's
        /// `runtime::Context` inherits it and exits with
        /// `StatusCode::Cancelled` once it has passed. `time_point::max()`
        /// disarms it; default: no deadline.
        /// CAVEAT: compiled code only observes the deadline at storage/call
        /// ops, so pure-compute loops don't check the deadline; deadlines are
        /// only reliable on an InterpreterOnly VM.
        void set_execution_deadline(
            std::chrono::steady_clock::time_point const deadline) noexcept
        {
            if (deadline == std::chrono::steady_clock::time_point::max()) {
                deadline_ns_ = runtime::Context::no_deadline;
                return;
            }
            deadline_ns_ = std::chrono::duration_cast<std::chrono::nanoseconds>(
                               deadline.time_since_epoch())
                               .count();
        }

        int64_t execution_deadline() const noexcept
        {
            return deadline_ns_;
        }

        /// True if any frame executed with this host was aborted because the
        /// execution deadline passed. Unlike the transaction's status code,
        /// this cannot be confused with other failures (e.g. a precompile
        /// returning EVMC_REJECTED).
        bool execution_cancelled() const noexcept
        {
            return execution_cancelled_;
        }

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

        void note_execution_cancelled() noexcept
        {
            execution_cancelled_ = true;
        }

        runtime::Context *runtime_context_{nullptr};
        mutable std::exception_ptr active_exception_;
        int64_t deadline_ns_{runtime::Context::no_deadline};
        bool execution_cancelled_{false};
    };
}
