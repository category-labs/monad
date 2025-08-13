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
#include <category/core/withdrawal.hpp>

template <>
struct quill::copy_loggable<monad::Withdrawal> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Withdrawal> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Withdrawal const &w, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Withdrawal{{"
            "Index={} "
            "Validator Index={} "
            "Amount={} "
            "Recipient={}"
            "}}",
            w.index,
            w.validator_index,
            w.amount,
            w.recipient);
        return ctx.out();
    }
};
