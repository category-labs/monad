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

#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>

#include <optional>

MONAD_STAKING_NAMESPACE_BEGIN

// RFC 9380, Sections 5 and 8.7, Appendices E.1, F.2, F.2.1.2, and G.1.
// https://www.rfc-editor.org/rfc/rfc9380
// These helpers process public registration transcripts; arithmetic is variable
// time.
std::optional<secp256k1_pubkey>
hash_to_secp256k1(byte_string_view message, byte_string_view dst);

// RFC 9380, Section 5.3.1. Returns one scalar in [0, secp256k1_order).
std::optional<bytes32_t>
hash_to_secp256k1_scalar(byte_string_view message, byte_string_view dst);

MONAD_STAKING_NAMESPACE_END
