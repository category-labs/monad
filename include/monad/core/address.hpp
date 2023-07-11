#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

#include <ethash/keccak.hpp>
#include <evmc/evmc.hpp>

#include <bit>

MONAD_NAMESPACE_BEGIN

using address_t = ::evmc::address;

static_assert(sizeof(address_t) == 20);
static_assert(alignof(address_t) == 1);

struct Address
{
    using hash_t = bytes32_t;
    hash_t hash;
    address_t address;
};

static_assert(sizeof(Address) == 52);
static_assert(alignof(Address) == 1);

inline constexpr bool operator==(const Address &a, const Address &b) noexcept
{
    return a.hash == b.hash && a.address == b.address;
}

inline Address construct_address(const address_t &a)
{
    return Address{
        .hash = std::bit_cast<Address::hash_t>(
            ethash::keccak256(a.bytes, sizeof(a.bytes))),
        .address = a};
}

MONAD_NAMESPACE_END
