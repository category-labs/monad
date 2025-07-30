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

#include <evmc/evmc.h>

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#pragma pack(push, 1)

struct monad_validator
{
    uint8_t secp_pubkey[33];
    uint8_t bls_pubkey[48];
    evmc_uint256be stake;
};

static_assert(sizeof(monad_validator) == 113);

struct monad_validator_set
{
    monad_validator *valset;
    uint64_t length;
};

static_assert(sizeof(monad_validator_set) == 16);

#pragma pack(pop)

struct monad_validator_set monad_alloc_valset(size_t size);
void monad_free_valset(monad_validator_set);

#ifdef __cplusplus
}
#endif
