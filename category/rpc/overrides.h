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

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_state_override;

struct monad_state_override *monad_state_override_create();

void monad_state_override_destroy(struct monad_state_override *);

void add_override_address(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len);

void set_override_balance(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *balance, size_t balance_len);

void set_override_nonce(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint64_t nonce);

void set_override_code(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *code, size_t code_len);

void set_override_state_diff(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *key, size_t key_len, uint8_t const *value, size_t value_len);

void set_override_state(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *key, size_t key_len, uint8_t const *value, size_t value_len);

struct monad_block_override;

struct monad_block_override *monad_block_override_create();

void monad_block_override_destroy(struct monad_block_override *);

void set_block_override_number(struct monad_block_override *, uint64_t number);

void set_block_override_time(struct monad_block_override *, uint64_t time);

void set_block_override_gas_limit(
    struct monad_block_override *, uint64_t gas_limit);

void set_block_override_fee_recipient(
    struct monad_block_override *, uint8_t const *addr, size_t addr_len);

void set_block_override_prev_randao(
    struct monad_block_override *, uint8_t const *randao, size_t randao_len);

void set_block_override_base_fee_per_gas(
    struct monad_block_override *, uint8_t const *fee, size_t fee_len);

void set_block_override_blob_base_fee(
    struct monad_block_override *, uint8_t const *fee, size_t fee_len);

#ifdef __cplusplus
}
#endif
