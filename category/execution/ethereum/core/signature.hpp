#pragma once

#include <category/core/int.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct SignatureAndChain
{
    uint256_t r{};
    uint256_t s{};
    std::optional<uint256_t> chain_id{};
    uint8_t y_parity{};

    void from_v(uint256_t const &);

    friend bool
    operator==(SignatureAndChain const &, SignatureAndChain const &) = default;
};

static_assert(sizeof(SignatureAndChain) == 112);
static_assert(alignof(SignatureAndChain) == 8);

uint256_t get_v(SignatureAndChain const &) noexcept;

MONAD_NAMESPACE_END
