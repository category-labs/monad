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

#include <category/execution/monad/staking/config.hpp>
#include <category/vm/evm/monad/revision.h>

#include <optional>
#include <vector>

#include <evmc/evmc.h>
#include <stdint.h>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

MONAD_NAMESPACE_END

MONAD_STAKING_NAMESPACE_BEGIN

struct Validator
{
    uint8_t secp_pubkey[33];
    uint8_t bls_pubkey[48];
    evmc_uint256be stake;
};

std::optional<std::vector<Validator>> read_valset(
    monad_revision rev, mpt::Db &db, size_t block_num,
    uint64_t requested_epoch);

MONAD_STAKING_NAMESPACE_END
