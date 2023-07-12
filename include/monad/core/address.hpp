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
    bytes32_t hash;
    address_t address;

    constexpr bool operator==(Address const &) const = default;

    explicit inline Address(const address_t &a)
        : hash(std::bit_cast<bytes32_t>(
              ethash::keccak256(a.bytes, sizeof(address_t::bytes))))
        , address(a)
    {
    }
};

static_assert(sizeof(Address) == 52);
static_assert(alignof(Address) == 1);

MONAD_NAMESPACE_END
