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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>
#include <utility>

MONAD_NAMESPACE_BEGIN

class State;
struct CallTracerBase;

// TODO(cmcl): Stub precompile address
inline constexpr Address ALE_CA = Address{0x1A7E};

// Encoding the associated data
// abi.encode("monad-sealed-blob-v1", dest_domain, to, app_ctx).
byte_string sealed_blob_ad(
    uint64_t dest_domain, Address const &to, byte_string_view app_ctx);

class ApplicationEncryptionContract
{
    [[maybe_unused]] State &state_;
    [[maybe_unused]] CallTracerBase &call_tracer_;
    [[maybe_unused]] bool log_native_transfers_;

public:
    ApplicationEncryptionContract(
        State &, CallTracerBase &, bool log_native_transfers = false);

    using PrecompileFunc =
        Result<byte_string> (ApplicationEncryptionContract::*)(
            byte_string_view, Address const &, uint256_be_t const &);

    template <Traits traits>
    static std::pair<PrecompileFunc, uint64_t>
    precompile_dispatch(byte_string_view &);

    Result<byte_string> precompile_seal(
        byte_string_view input, Address const &msg_sender,
        uint256_be_t const &msg_value);

    Result<byte_string> precompile_unseal(
        byte_string_view input, Address const &msg_sender,
        uint256_be_t const &msg_value);

    Result<byte_string> precompile_fallback(
        byte_string_view, Address const &, uint256_be_t const &);
};

MONAD_NAMESPACE_END
