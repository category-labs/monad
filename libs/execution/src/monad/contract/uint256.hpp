#pragma once

#include <evmc/evmc.h>
#include <intx/intx.hpp>
#include <monad/config.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

#pragma once

#include <evmc/evmc.h>
#include <intx/intx.hpp>

struct Uint256BE;

struct Uint256Native : public uint256_t
{
    using uint256_t::uint256_t;
    Uint256Native(uint256_t x);

    Uint256Native &add(uint256_t const &other);
    Uint256Native &sub(uint256_t const &other);
    Uint256BE to_be() const noexcept;
};

struct Uint256BE
{
    evmc_uint256be raw;

    constexpr Uint256BE() = default;
    Uint256BE(evmc_uint256be r);

    bool operator==(Uint256BE const &other) const noexcept;
    Uint256Native native() const noexcept;
};

MONAD_NAMESPACE_END
