#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

inline constexpr address_t ripemd_address{3};

template <evmc_revision rev>
bool is_precompile(address_t const &) noexcept;

template <evmc_revision rev>
std::optional<evmc::Result> check_call_precompile(evmc_message const &);

MONAD_NAMESPACE_END
