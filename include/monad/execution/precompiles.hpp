#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/revision.hpp>

#include <silkpre/precompile.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <optional>

MONAD_EVM_NAMESPACE_BEGIN

struct CallParameters;
enum class Status;

MONAD_EVM_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

inline constexpr Address ripemd_address{3};

template <evmc_revision rev>
bool is_precompile(Address const &) noexcept;

template <evmc_revision rev>
std::optional<evmc::Result> check_call_precompile(evmc_message const &);

using PrecompileResult = std::tuple<evm::Status, uint64_t, byte_string>;

template <evm::Revision rev>
std::optional<PrecompileResult>
check_call_precompile(evm::CallParameters const &);

MONAD_NAMESPACE_END
