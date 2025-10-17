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
#include <category/execution/ethereum/core/address.hpp>

#include <span>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

template <>
struct quill::copy_loggable<monad::Address> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Address> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Address const &value, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        return ctx.out();
    }
};
