#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/precompiles.hpp>

#include <silkpre/precompile.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/helpers.h>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

consteval unsigned num_precompiles(evmc_revision const rev)
{
    switch (rev) {
    case EVMC_FRONTIER:
    case EVMC_HOMESTEAD:
    case EVMC_TANGERINE_WHISTLE:
    case EVMC_SPURIOUS_DRAGON:
        return 4;
    case EVMC_BYZANTIUM:
    case EVMC_CONSTANTINOPLE:
    case EVMC_PETERSBURG:
        return 8;
    case EVMC_ISTANBUL:
    case EVMC_BERLIN:
    case EVMC_LONDON:
    case EVMC_PARIS:
    case EVMC_SHANGHAI:
        return 9;
    default:
        MONAD_ASSERT(false);
    }
}

template <evmc_revision rev>
bool is_precompile(Address const &address) noexcept
{
    static constexpr auto max_address = Address{num_precompiles(rev)};

    if (MONAD_LIKELY(address > max_address)) {
        return false;
    }

    if (MONAD_UNLIKELY(evmc::is_zero(address))) {
        return false;
    }

    return true;
}

EXPLICIT_EVMC_REVISION(is_precompile);

template <evmc_revision rev>
std::optional<evmc::Result> check_call_precompile(evmc_message const &msg)
{
    auto const &address = msg.code_address;

    if (!is_precompile<rev>(address)) {
        return std::nullopt;
    }

    auto const i = address.bytes[sizeof(address.bytes) - 1];

    auto const gas_func = kSilkpreContracts[i - 1].gas;

    auto const cost = gas_func(msg.input_data, msg.input_size, rev);

    if (MONAD_UNLIKELY(std::cmp_less(msg.gas, cost))) {
        return evmc::Result{evmc_status_code::EVMC_OUT_OF_GAS};
    }

    auto const run_func = kSilkpreContracts[i - 1].run;

    auto const output = run_func(msg.input_data, msg.input_size);

    if (MONAD_UNLIKELY(!output.data)) {
        return evmc::Result{evmc_status_code::EVMC_PRECOMPILE_FAILURE};
    }

    return evmc::Result{evmc_result{
        .status_code = evmc_status_code::EVMC_SUCCESS,
        .gas_left = msg.gas - static_cast<int64_t>(cost),
        .gas_refund = 0,
        .output_data = output.data,
        .output_size = output.size,
        .release = evmc_free_result_memory}};
}

EXPLICIT_EVMC_REVISION(check_call_precompile);

MONAD_NAMESPACE_END
