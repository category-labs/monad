// Copyright (C) 2026 Category Labs, Inc.
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

// Plaintext benchmark control: leaves are raw transactions, with the same L2
// chain rules, state blinding and anchors as encrypted suites. Comparing
// against it isolates encryption costs; the mainnet guest would not. Never
// deploy: all sequenced transactions are public.

#include <category/core/config.hpp>

#include <optional>
#include <span>
#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct L2PlaintextSuite
{
    /// Nothing about the block reaches a leaf.
    struct Context
    {
    };

    /// No secret affects plaintext decoding, so any 32-byte witness value
    /// produces the same transaction bytes.
    struct Secret
    {
    };

    static constexpr std::string_view LABEL = "monad-l2/plaintext/v1/";

    static std::optional<Secret>
    bind_secret(Context const &, std::span<unsigned char const, 32>)
    {
        return Secret{};
    }

    /// Never a rejection at this stage: a leaf that is not a transaction is
    /// rejected by the decoder that reads it next, as any plaintext is.
    static bool decrypt(
        Context const &, Secret const &,
        std::span<unsigned char const> const leaf,
        std::vector<unsigned char> &plain)
    {
        plain.assign(leaf.begin(), leaf.end());
        return true;
    }
};

MONAD_NAMESPACE_END
