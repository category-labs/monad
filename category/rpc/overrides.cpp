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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/rpc/overrides.h>
#include <category/rpc/overrides.hpp>

#include <cstdint>
#include <cstring>
#include <new>
#include <vector>

using namespace monad;

monad_override_status_code_t
monad_state_override_create(monad_state_override **const out)
{
    if (!out) {
        return MONAD_OVERRIDE_EINVAL;
    }

    try {
        *out = new monad_state_override();
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }

    return MONAD_OVERRIDE_OK;
}

void monad_state_override_destroy(monad_state_override *const m)
{
    delete m;
}

monad_override_status_code_t add_override_address(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len)
{
    if (!m || !addr || addr_len != sizeof(Address)) {
        return MONAD_OVERRIDE_EINVAL;
    }

    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));

    if (m->override_sets.find(address) != m->override_sets.end()) {
        return MONAD_OVERRIDE_EEXIST;
    }
    try {
        m->override_sets.emplace(
            address, monad_state_override::monad_state_override_object{});
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }
    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_override_balance(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const balance,
    size_t const balance_len)
{
    if (!m || !addr || addr_len != sizeof(Address) || !balance ||
        balance_len != sizeof(uint256_t)) {
        return MONAD_OVERRIDE_EINVAL;
    }

    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    if (m->override_sets.find(address) == m->override_sets.end()) {
        return MONAD_OVERRIDE_ENOENT;
    }
    m->override_sets[address].balance = load_be_unsafe<uint256_t>(balance);

    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_override_nonce(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint64_t const nonce)
{
    if (!m || !addr || addr_len != sizeof(Address)) {
        return MONAD_OVERRIDE_EINVAL;
    }

    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    if (m->override_sets.find(address) == m->override_sets.end()) {
        return MONAD_OVERRIDE_ENOENT;
    }
    m->override_sets[address].nonce = nonce;

    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_override_code(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const code, size_t const code_len)
{
    if (!m || !addr || addr_len != sizeof(Address) || !code) {
        return MONAD_OVERRIDE_EINVAL;
    }

    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    if (m->override_sets.find(address) == m->override_sets.end()) {
        return MONAD_OVERRIDE_ENOENT;
    }
    m->override_sets[address].code = {code, code + code_len};

    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_override_state_diff(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const key, size_t const key_len,
    uint8_t const *const value, size_t const value_len)
{
    if (!m || !addr || addr_len != sizeof(Address) || !key ||
        key_len != sizeof(bytes32_t) || !value ||
        value_len != sizeof(bytes32_t)) {
        return MONAD_OVERRIDE_EINVAL;
    }

    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    if (m->override_sets.find(address) == m->override_sets.end()) {
        return MONAD_OVERRIDE_ENOENT;
    }

    bytes32_t k;
    std::memcpy(k.bytes, key, sizeof(bytes32_t));

    bytes32_t v;
    std::memcpy(v.bytes, value, sizeof(bytes32_t));

    auto &state_object = m->override_sets[address].state_diff;
    if (state_object.find(k) != state_object.end()) {
        return MONAD_OVERRIDE_EEXIST;
    }
    try {
        state_object.emplace(k, v);
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }

    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_override_state(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const key, size_t const key_len,
    uint8_t const *const value, size_t const value_len)
{
    if (!m || !addr || addr_len != sizeof(Address) || !key ||
        key_len != sizeof(bytes32_t) || !value ||
        value_len != sizeof(bytes32_t)) {
        return MONAD_OVERRIDE_EINVAL;
    }

    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    if (m->override_sets.find(address) == m->override_sets.end()) {
        return MONAD_OVERRIDE_ENOENT;
    }

    bytes32_t k;
    std::memcpy(k.bytes, key, sizeof(bytes32_t));

    bytes32_t v;
    std::memcpy(v.bytes, value, sizeof(bytes32_t));

    auto &state_object = m->override_sets[address].state;
    if (state_object.find(k) != state_object.end()) {
        return MONAD_OVERRIDE_EEXIST;
    }

    try {
        state_object.emplace(k, v);
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }

    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t monad_state_override_vec_create(
    size_t const size, monad_state_override_vec **const out)
{
    if (!out) {
        return MONAD_OVERRIDE_EINVAL;
    }

    try {
        *out = new monad_state_override_vec(size);
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }

    return MONAD_OVERRIDE_OK;
}

void monad_state_override_vec_destroy(struct monad_state_override_vec *v)
{
    if (v) {
        delete[] v->overrides;
        delete v;
    }
}

monad_override_status_code_t add_override_address_at(
    struct monad_state_override_vec *v, size_t index, uint8_t const *addr,
    size_t addr_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return add_override_address(&v->overrides[index], addr, addr_len);
}

monad_override_status_code_t set_override_balance_at(
    struct monad_state_override_vec *v, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *balance, size_t balance_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_override_balance(
        &v->overrides[index], addr, addr_len, balance, balance_len);
}

monad_override_status_code_t set_override_nonce_at(
    struct monad_state_override_vec *v, size_t index, uint8_t const *addr,
    size_t addr_len, uint64_t nonce)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_override_nonce(&v->overrides[index], addr, addr_len, nonce);
}

monad_override_status_code_t set_override_code_at(
    struct monad_state_override_vec *v, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *code, size_t code_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_override_code(
        &v->overrides[index], addr, addr_len, code, code_len);
}

monad_override_status_code_t set_override_state_diff_at(
    struct monad_state_override_vec *v, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *key, size_t key_len, uint8_t const *value,
    size_t value_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_override_state_diff(
        &v->overrides[index], addr, addr_len, key, key_len, value, value_len);
}

monad_override_status_code_t set_override_state_at(
    struct monad_state_override_vec *v, size_t index, uint8_t const *addr,
    size_t addr_len, uint8_t const *key, size_t key_len, uint8_t const *value,
    size_t value_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_override_state(
        &v->overrides[index], addr, addr_len, key, key_len, value, value_len);
}

monad_override_status_code_t
monad_block_override_create(monad_block_override **const out)
{
    if (!out) {
        return MONAD_OVERRIDE_EINVAL;
    }

    try {
        *out = new monad_block_override();
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }
    return MONAD_OVERRIDE_OK;
}

void monad_block_override_destroy(monad_block_override *const m)
{
    delete m;
}

monad_override_status_code_t
set_block_override_number(monad_block_override *const m, uint64_t const number)
{
    if (!m) {
        return MONAD_OVERRIDE_EINVAL;
    }

    if (m->number.has_value()) {
        return MONAD_OVERRIDE_EEXIST;
    }

    m->number = number;
    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t
set_block_override_time(monad_block_override *const m, uint64_t const time)
{
    if (!m) {
        return MONAD_OVERRIDE_EINVAL;
    }
    if (m->time.has_value()) {
        return MONAD_OVERRIDE_EEXIST;
    }
    m->time = time;
    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_block_override_gas_limit(
    monad_block_override *const m, uint64_t const gas_limit)
{
    if (!m) {
        return MONAD_OVERRIDE_EINVAL;
    }
    if (m->gas_limit.has_value()) {
        return MONAD_OVERRIDE_EEXIST;
    }
    m->gas_limit = gas_limit;
    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_block_override_fee_recipient(
    monad_block_override *const m, uint8_t const *const addr,
    size_t const addr_len)
{
    if (!m || !addr || addr_len != sizeof(Address)) {
        return MONAD_OVERRIDE_EINVAL;
    }
    if (m->fee_recipient.has_value()) {
        return MONAD_OVERRIDE_EEXIST;
    }
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    m->fee_recipient = address;
    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_block_override_prev_randao(
    monad_block_override *const m, uint8_t const *const randao,
    size_t const randao_len)
{
    if (!m || !randao || randao_len != sizeof(bytes32_t)) {
        return MONAD_OVERRIDE_EINVAL;
    }
    if (m->prev_randao.has_value()) {
        return MONAD_OVERRIDE_EEXIST;
    }
    bytes32_t val;
    std::memcpy(val.bytes, randao, sizeof(bytes32_t));
    m->prev_randao = val;
    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t set_block_override_base_fee_per_gas(
    monad_block_override *const m, uint8_t const *const fee,
    size_t const fee_len)
{
    if (!m || !fee || fee_len != sizeof(uint256_t)) {
        return MONAD_OVERRIDE_EINVAL;
    }
    if (m->base_fee_per_gas.has_value()) {
        return MONAD_OVERRIDE_EEXIST;
    }
    m->base_fee_per_gas = load_be_unsafe<uint256_t>(fee);
    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t add_block_override_withdrawal(
    struct monad_block_override *const m, uint64_t index,
    uint64_t validator_index, uint64_t amount, uint8_t const *recipient_addr,
    size_t recipient_addr_len)
{
    if (!m || !recipient_addr || recipient_addr_len != sizeof(Address)) {
        return MONAD_OVERRIDE_EINVAL;
    }

    Address recipient;
    std::memcpy(recipient.bytes, recipient_addr, sizeof(Address));

    if (!m->withdrawals.has_value()) {
        m->withdrawals = std::vector<Withdrawal>{};
    }

    try {
        m->withdrawals->emplace_back(Withdrawal{
            .index = index,
            .validator_index = validator_index,
            .amount = amount,
            .recipient = recipient,
        });
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }

    return MONAD_OVERRIDE_OK;
}

monad_override_status_code_t monad_block_override_vec_create(
    size_t const size, monad_block_override_vec **const out)
{
    if (!out) {
        return MONAD_OVERRIDE_EINVAL;
    }

    try {
        *out = new monad_block_override_vec(size);
    }
    catch (std::bad_alloc const &) {
        return MONAD_OVERRIDE_ENOMEM;
    }
    catch (...) {
        return MONAD_OVERRIDE_EUNKNOWN;
    }

    return MONAD_OVERRIDE_OK;
}

void monad_block_override_vec_destroy(struct monad_block_override_vec *v)
{
    if (v) {
        delete[] v->overrides;
        delete v;
    }
}

monad_override_status_code_t set_block_override_number_at(
    struct monad_block_override_vec *v, size_t index, uint64_t number)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_block_override_number(&v->overrides[index], number);
}

monad_override_status_code_t set_block_override_time_at(
    struct monad_block_override_vec *v, size_t index, uint64_t time)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_block_override_time(&v->overrides[index], time);
}

monad_override_status_code_t set_block_override_gas_limit_at(
    struct monad_block_override_vec *v, size_t index, uint64_t gas_limit)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_block_override_gas_limit(&v->overrides[index], gas_limit);
}

monad_override_status_code_t set_block_override_fee_recipient_at(
    struct monad_block_override_vec *v, size_t index, uint8_t const *addr,
    size_t addr_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_block_override_fee_recipient(
        &v->overrides[index], addr, addr_len);
}

monad_override_status_code_t set_block_override_prev_randao_at(
    struct monad_block_override_vec *v, size_t index, uint8_t const *randao,
    size_t randao_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_block_override_prev_randao(
        &v->overrides[index], randao, randao_len);
}

monad_override_status_code_t set_block_override_base_fee_per_gas_at(
    struct monad_block_override_vec *v, size_t index, uint8_t const *fee,
    size_t fee_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return set_block_override_base_fee_per_gas(
        &v->overrides[index], fee, fee_len);
}

monad_override_status_code_t add_block_override_withdrawal_at(
    struct monad_block_override_vec *v, size_t index, uint64_t withdrawal_index,
    uint64_t validator_index, uint64_t amount, uint8_t const *recipient_addr,
    size_t recipient_addr_len)
{
    if (!v || index >= v->size) {
        return MONAD_OVERRIDE_EINVAL;
    }
    return add_block_override_withdrawal(
        &v->overrides[index],
        withdrawal_index,
        validator_index,
        amount,
        recipient_addr,
        recipient_addr_len);
}
