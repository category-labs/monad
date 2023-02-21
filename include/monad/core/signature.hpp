#pragma once

#include <monad/core/int.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct SignatureAndChain
{
    uint256_t r{};
    uint256_t s{};
    std::optional<uint64_t> chain_id{};
    bool odd_y_parity{};

    void from_v(uint64_t const &v);
};

static_assert(sizeof(SignatureAndChain) == 88);
static_assert(alignof(SignatureAndChain) == 8);

uint64_t get_v(SignatureAndChain const &sc) noexcept;

MONAD_NAMESPACE_END
