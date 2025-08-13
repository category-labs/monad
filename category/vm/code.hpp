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

#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/interpreter/intercode.hpp>

#include <atomic>

namespace monad::vm
{
    using interpreter::Intercode;
    using SharedIntercode = std::shared_ptr<Intercode const>;

    template <typename... Args>
    inline SharedIntercode make_shared_intercode(Args &&...args)
    {
        return std::make_shared<Intercode const>(std::forward<Args>(args)...);
    }

    inline SharedIntercode
    make_shared_intercode(std::initializer_list<uint8_t> a)
    {
        return std::make_shared<Intercode const>(a);
    }

    using compiler::native::Nativecode;
    using SharedNativecode = std::shared_ptr<Nativecode const>;

    class Varcode
    {
    public:
        explicit Varcode(SharedIntercode icode)
            : intercode_gas_used_{0}
            , intercode_{std::move(icode)}
        {
        }

        Varcode(SharedIntercode icode, SharedNativecode ncode)
            : intercode_gas_used_{0}
            , intercode_{std::move(icode)}
            , nativecode_{std::move(ncode)}
        {
        }

        Varcode(Varcode const &) = delete;
        Varcode &operator=(Varcode const &) = delete;

        std::uint64_t intercode_gas_used(std::uint64_t gas_used)
        {
            return gas_used + intercode_gas_used_.fetch_add(
                                  gas_used, std::memory_order_acq_rel);
        }

        std::uint64_t get_intercode_gas_used()
        {
            return intercode_gas_used_.load(std::memory_order_acquire);
        }

        /// Get corresponding intercode.
        /// Can be assumed to always return a non-null result.
        SharedIntercode const &intercode() const
        {
            return intercode_;
        }

        /// Get corresponding nativecode. Returns null if no native code.
        SharedNativecode const &nativecode() const
        {
            return nativecode_;
        }

    private:
        std::atomic<std::uint64_t> intercode_gas_used_;
        SharedIntercode intercode_;
        SharedNativecode nativecode_;
    };

    using SharedVarcode = std::shared_ptr<Varcode>;
}
