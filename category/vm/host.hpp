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
#include <category/core/assert.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.hpp>

#include <cstddef>
#include <exception>
#include <vector>

namespace monad::vm
{
    class VM;

    class Host : public evmc::Host
    {
        friend class VM;

    public:
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

        Address call_frame_sender(size_t const depth) const noexcept
        {
            MONAD_ASSERT(depth < call_frame_senders_.size());
            return call_frame_senders_[depth];
        }

        void set_call_frame_sender(size_t const depth, Address const &sender)
        {
            if (depth >= call_frame_senders_.size()) {
                call_frame_senders_.resize(depth + 1);
            }
            call_frame_senders_[depth] = sender;
        }

    private:
        template <Traits traits>
        void enter_call_frame(runtime::Context const &ctx)
        {
            if constexpr (traits::mip_18_active()) {
                set_call_frame_sender(
                    static_cast<size_t>(ctx.env.depth), ctx.env.sender);
            }
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
        std::vector<Address> call_frame_senders_;
    };
}
