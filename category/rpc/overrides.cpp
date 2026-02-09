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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/rpc/overrides.h>
#include <category/rpc/overrides.hpp>

#include <intx/intx.hpp>

#include <cstdint>
#include <cstring>

using namespace monad;

monad_state_override *monad_state_override_create()
{
    monad_state_override *const m = new monad_state_override();

    return m;
}

void monad_state_override_destroy(monad_state_override *const m)
{
    MONAD_ASSERT(m);
    delete m;
}

void add_override_address(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));

    MONAD_ASSERT(m->override_sets.find(address) == m->override_sets.end());
    m->override_sets.emplace(
        address, monad_state_override::monad_state_override_object{});
}

void set_override_balance(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const balance,
    size_t const balance_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(balance);
    MONAD_ASSERT(balance_len == sizeof(uint256_t));
    m->override_sets[address].balance =
        intx::be::unsafe::load<uint256_t>(balance);
}

void set_override_nonce(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint64_t const nonce)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    m->override_sets[address].nonce = nonce;
}

void set_override_code(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const code, size_t const code_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(code);
    m->override_sets[address].code = {code, code + code_len};
}

void set_override_state_diff(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const key, size_t const key_len,
    uint8_t const *const value, size_t const value_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(key);
    MONAD_ASSERT(key_len == sizeof(bytes32_t));
    bytes32_t k;
    std::memcpy(k.bytes, key, sizeof(bytes32_t));

    MONAD_ASSERT(value);
    MONAD_ASSERT(value_len == sizeof(bytes32_t));
    bytes32_t v;
    std::memcpy(v.bytes, value, sizeof(bytes32_t));

    auto &state_object = m->override_sets[address].state_diff;
    MONAD_ASSERT(state_object.find(k) == state_object.end());
    state_object.emplace(k, v);
}

void set_override_state(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const key, size_t const key_len,
    uint8_t const *const value, size_t const value_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(key);
    MONAD_ASSERT(key_len == sizeof(bytes32_t));
    bytes32_t k;
    std::memcpy(k.bytes, key, sizeof(bytes32_t));

    MONAD_ASSERT(value);
    MONAD_ASSERT(value_len == sizeof(bytes32_t));
    bytes32_t v;
    std::memcpy(v.bytes, value, sizeof(bytes32_t));

    auto &state_object = m->override_sets[address].state;
    MONAD_ASSERT(state_object.find(k) == state_object.end());
    state_object.emplace(k, v);
}

monad_block_override *monad_block_override_create()
{
    return new monad_block_override();
}

void monad_block_override_destroy(monad_block_override *const m)
{
    MONAD_ASSERT(m);
    delete m;
}

void set_block_override_number(
    monad_block_override *const m, uint64_t const number)
{
    MONAD_ASSERT(m);
    MONAD_ASSERT(!m->number.has_value());
    m->number = number;
}

void set_block_override_time(monad_block_override *const m, uint64_t const time)
{
    MONAD_ASSERT(m);
    MONAD_ASSERT(!m->time.has_value());
    m->time = time;
}

void set_block_override_gas_limit(
    monad_block_override *const m, uint64_t const gas_limit)
{
    MONAD_ASSERT(m);
    MONAD_ASSERT(!m->gas_limit.has_value());
    m->gas_limit = gas_limit;
}

void set_block_override_fee_recipient(
    monad_block_override *const m, uint8_t const *const addr,
    size_t const addr_len)
{
    MONAD_ASSERT(m);
    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    MONAD_ASSERT(!m->fee_recipient.has_value());
    Address address;
    std::memcpy(address.bytes, addr, sizeof(Address));
    m->fee_recipient = address;
}

void set_block_override_prev_randao(
    monad_block_override *const m, uint8_t const *const randao,
    size_t const randao_len)
{
    MONAD_ASSERT(m);
    MONAD_ASSERT(randao);
    MONAD_ASSERT(randao_len == sizeof(bytes32_t));
    MONAD_ASSERT(!m->prev_randao.has_value());
    bytes32_t val;
    std::memcpy(val.bytes, randao, sizeof(bytes32_t));
    m->prev_randao = val;
}

void set_block_override_base_fee_per_gas(
    monad_block_override *const m, uint8_t const *const fee,
    size_t const fee_len)
{
    MONAD_ASSERT(m);
    MONAD_ASSERT(fee);
    MONAD_ASSERT(fee_len == sizeof(uint256_t));
    MONAD_ASSERT(!m->base_fee_per_gas.has_value());
    m->base_fee_per_gas = intx::be::unsafe::load<uint256_t>(fee);
}

void set_block_override_blob_base_fee(
    monad_block_override *const m, uint8_t const *const fee,
    size_t const fee_len)
{
    MONAD_ASSERT(m);
    MONAD_ASSERT(fee);
    MONAD_ASSERT(fee_len == sizeof(uint256_t));
    MONAD_ASSERT(!m->blob_base_fee.has_value());
    m->blob_base_fee = intx::be::unsafe::load<uint256_t>(fee);
}
