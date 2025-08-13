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
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <quill/Quill.h>

template <>
struct quill::copy_loggable<monad::SignatureAndChain> : std::true_type
{
};

template <>
struct fmt::formatter<monad::SignatureAndChain> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::SignatureAndChain const &sc, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "SignatureAndChain{{"
            "r={} "
            "s={} "
            "chain_id={} "
            "y_parity={}"
            "}}",
            sc.r,
            sc.s,
            sc.chain_id,
            sc.y_parity);
        return ctx.out();
    }
};
