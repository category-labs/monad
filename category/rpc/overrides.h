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

typedef enum monad_override_status_code
{
    MONAD_OVERRIDE_OK = 0,
    MONAD_OVERRIDE_EINVAL = 1,
    MONAD_OVERRIDE_ENOMEM = 2,
    MONAD_OVERRIDE_EEXIST = 3,
    MONAD_OVERRIDE_ENOENT = 4,
    MONAD_OVERRIDE_EUNKNOWN = 5,
} monad_override_status_code_t;

struct monad_state_override;

[[nodiscard]]
monad_override_status_code_t
monad_state_override_create(struct monad_state_override **);

void monad_state_override_destroy(struct monad_state_override *);

[[nodiscard]]
monad_override_status_code_t add_override_address(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len);

[[nodiscard]]
monad_override_status_code_t set_override_balance(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *balance, size_t balance_len);

[[nodiscard]]
monad_override_status_code_t set_override_nonce(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint64_t nonce);

[[nodiscard]]
monad_override_status_code_t set_override_code(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *code, size_t code_len);

[[nodiscard]]
monad_override_status_code_t set_override_state_diff(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *key, size_t key_len, uint8_t const *value, size_t value_len);

[[nodiscard]]
monad_override_status_code_t set_override_state(
    struct monad_state_override *, uint8_t const *addr, size_t addr_len,
    uint8_t const *key, size_t key_len, uint8_t const *value, size_t value_len);

struct monad_state_override_vec;

[[nodiscard]]
monad_override_status_code_t monad_state_override_vec_create(
    size_t size, struct monad_state_override_vec **);

void monad_state_override_vec_destroy(struct monad_state_override_vec *);

[[nodiscard]]
monad_override_status_code_t add_override_address_at(
    struct monad_state_override_vec *, size_t index, uint8_t const *addr,
    size_t addr_len);

[[nodiscard]]
monad_override_status_code_t set_override_balance_at(
    struct monad_state_override_vec *, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *balance, size_t balance_len);

[[nodiscard]]
monad_override_status_code_t set_override_nonce_at(
    struct monad_state_override_vec *, size_t index, uint8_t const *addr,
    size_t addr_len, uint64_t nonce);

[[nodiscard]]
monad_override_status_code_t set_override_code_at(
    struct monad_state_override_vec *, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *code, size_t code_len);

[[nodiscard]]
monad_override_status_code_t set_override_state_diff_at(
    struct monad_state_override_vec *, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *key, size_t key_len, uint8_t const *value,
    size_t value_len);

[[nodiscard]]
monad_override_status_code_t set_override_state_at(
    struct monad_state_override_vec *, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *key, size_t key_len, uint8_t const *value,
    size_t value_len);

struct monad_block_override;

[[nodiscard]]
monad_override_status_code_t
monad_block_override_create(struct monad_block_override **);

void monad_block_override_destroy(struct monad_block_override *);

[[nodiscard]]
monad_override_status_code_t
set_block_override_number(struct monad_block_override *, uint64_t number);

[[nodiscard]]
monad_override_status_code_t
set_block_override_time(struct monad_block_override *, uint64_t time);

[[nodiscard]]
monad_override_status_code_t
set_block_override_gas_limit(struct monad_block_override *, uint64_t gas_limit);

[[nodiscard]]
monad_override_status_code_t set_block_override_fee_recipient(
    struct monad_block_override *, uint8_t const *addr, size_t addr_len);

[[nodiscard]]
monad_override_status_code_t set_block_override_prev_randao(
    struct monad_block_override *, uint8_t const *randao, size_t randao_len);

[[nodiscard]]
monad_override_status_code_t set_block_override_base_fee_per_gas(
    struct monad_block_override *, uint8_t const *fee, size_t fee_len);

[[nodiscard]]
monad_override_status_code_t add_block_override_withdrawal(
    struct monad_block_override *, uint64_t index, uint64_t validator_index,
    uint64_t amount, uint8_t const *recipient_addr, size_t recipient_addr_len);

struct monad_block_override_vec;

[[nodiscard]]
monad_override_status_code_t monad_block_override_vec_create(
    size_t size, struct monad_block_override_vec **);

void monad_block_override_vec_destroy(struct monad_block_override_vec *);

[[nodiscard]]
monad_override_status_code_t set_block_override_number_at(
    struct monad_block_override_vec *, size_t index, uint64_t number);

[[nodiscard]]
monad_override_status_code_t set_block_override_time_at(
    struct monad_block_override_vec *, size_t index, uint64_t time);

[[nodiscard]]
monad_override_status_code_t set_block_override_gas_limit_at(
    struct monad_block_override_vec *, size_t index, uint64_t gas_limit);

[[nodiscard]]
monad_override_status_code_t set_block_override_fee_recipient_at(
    struct monad_block_override_vec *, size_t index, uint8_t const *addr,
    size_t addr_len);

[[nodiscard]]
monad_override_status_code_t set_block_override_prev_randao_at(
    struct monad_block_override_vec *, size_t index, uint8_t const *randao,
    size_t randao_len);

[[nodiscard]]
monad_override_status_code_t set_block_override_base_fee_per_gas_at(
    struct monad_block_override_vec *, size_t index, uint8_t const *fee,
    size_t fee_len);

[[nodiscard]]
monad_override_status_code_t add_block_override_withdrawal_at(
    struct monad_block_override_vec *, size_t index, uint64_t withdrawal_index,
    uint64_t validator_index, uint64_t amount, uint8_t const *recipient_addr,
    size_t recipient_addr_len);

#ifdef __cplusplus
}
#endif
