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

// The suite that does not encrypt: a leaf IS the transaction, the bytes a
// plaintext block would carry. It exists to measure the others. A guest built
// with it runs the L2 chain in every rule but one -- the same chain id, the
// same constant revision, the same unpriced gas, the same blinded header and
// anchor -- so what an encrypting suite costs over it is the encryption and
// nothing else. Comparing with the mainnet guest cannot isolate that: its
// chain prices gas, publishes another output and follows a fork schedule.
//
// Never a deployment. With it the transactions the L1 sequences are readable
// by anyone who reads the L1.

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

    /// Nothing to bind. The binding the encrypting suites need exists because
    /// another secret would decrypt to other transactions; here no secret
    /// reaches a plaintext, so a prover supplying any 32 bytes proves the same
    /// block.
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
