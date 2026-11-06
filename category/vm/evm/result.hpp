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

#include <category/core/address.hpp>
#include <category/vm/evm/status_code.h>

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <type_traits>

namespace monad::vm
{
    struct RawResult
    {
        monad_status_code status_code;
        int64_t gas_left;
        int64_t gas_refund;
        uint8_t const *output_data;
        size_t output_size;
        Address create_address;
    };

    static_assert(std::is_trivially_copyable_v<RawResult>);

    // Owns output_data, which is either null or safe to pass to std::free.
    class Result : private RawResult
    {
    public:
        using RawResult::create_address;
        using RawResult::gas_left;
        using RawResult::gas_refund;
        using RawResult::output_data;
        using RawResult::output_size;
        using RawResult::status_code;

        explicit Result(
            monad_status_code const code = MONAD_STATUS_INTERNAL_ERROR,
            int64_t const gas = 0, int64_t const refund = 0) noexcept
            : RawResult{code, gas, refund, nullptr, 0, {}}
        {
        }

        explicit Result(
            monad_status_code const code, int64_t const gas,
            int64_t const refund, Address const &address) noexcept
            : RawResult{code, gas, refund, nullptr, 0, address}
        {
        }

        explicit Result(
            monad_status_code const code, int64_t const gas,
            int64_t const refund, uint8_t const *const data,
            size_t const size) noexcept
            : Result{code, gas, refund}
        {
            if (size == 0) {
                return;
            }
            auto *const buf = static_cast<uint8_t *>(std::malloc(size));
            if (buf == nullptr) {
                static_cast<RawResult &>(*this) =
                    RawResult{MONAD_STATUS_OUT_OF_MEMORY, 0, 0, nullptr, 0, {}};
                return;
            }
            std::memcpy(buf, data, size);
            output_data = buf;
            output_size = size;
        }

        explicit Result(RawResult const &raw) noexcept
            : RawResult{raw}
        {
        }

        Result(Result &&other) noexcept
            : RawResult{other.release_raw()}
        {
        }

        Result &operator=(Result &&other) noexcept
        {
            if (this != &other) {
                std::free(const_cast<uint8_t *>(output_data));
                static_cast<RawResult &>(*this) = other.release_raw();
            }
            return *this;
        }

        ~Result()
        {
            std::free(const_cast<uint8_t *>(output_data));
        }

        [[nodiscard]] RawResult release_raw() noexcept
        {
            RawResult const raw = static_cast<RawResult const &>(*this);
            output_data = nullptr;
            output_size = 0;
            return raw;
        }
    };
}
