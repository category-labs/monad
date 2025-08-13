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

#include <category/core/basic_formatter.hpp>
#include <category/execution/ethereum/core/fmt/account_fmt.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>

#include <category/execution/ethereum/state2/state_deltas.hpp>

template <typename T>
struct quill::copy_loggable<monad::Delta<T>>
    : std::integral_constant<bool, detail::is_registered_copyable_v<T>>
{
};

template <>
struct quill::copy_loggable<monad::StateDelta> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::StateDeltas> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::Code> : std::true_type
{
};

template <>
struct fmt::formatter<monad::StateDelta> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::StateDelta const &state_delta, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");
        fmt::format_to(ctx.out(), "Account Delta: {} ", state_delta.account);
        fmt::format_to(ctx.out(), "Storage Deltas: {{");
        for (auto const &[key, storage_delta] : state_delta.storage) {
            fmt::format_to(
                ctx.out(), " Key: {}, Storage Delta: {}", key, storage_delta);
        }
        fmt::format_to(ctx.out(), "}}");
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::StateDeltas> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto
    format(monad::StateDeltas const &state_deltas, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");

        for (auto const &[address, state_delta] : state_deltas) {
            fmt::format_to(
                ctx.out(),
                " Address: {}, State Delta: {}",
                address,
                state_delta);
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::Code> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Code const &code, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{{");

        for (auto const &[code_hash, icode] : code) {
            MONAD_ASSERT(icode);
            fmt::format_to(
                ctx.out(),
                "Code Hash: {}, Code Value: 0x{:02x} ",
                code_hash,
                fmt::join(
                    std::as_bytes(std::span{icode->code(), icode->code_size()}),
                    ""));
        }
        fmt::format_to(ctx.out(), "}}");

        return ctx.out();
    }
};
