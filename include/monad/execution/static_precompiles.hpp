#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>

#include <evmc/evmc.hpp>

#include <tl/optional.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <
    class TState, concepts::fork_traits<TState> TTraits, class... TPrecompiles>
struct StaticPrecompiles
{
    using exec_func_t = evmc_result (*)(const evmc_message &) noexcept;

    static constexpr exec_func_t precompile_execs[] = {
        TPrecompiles::execute...};

    [[nodiscard]] static inline tl::optional<exec_func_t>
    static_precompile_exec_func(address_t const &addr) noexcept
    {
        const auto static_precompile_idx =
            [&]() -> tl::optional<const unsigned> {
            const auto last_address_i = sizeof(address_t) - 1u;
            for (auto i = 0u; i < last_address_i; ++i) {
                const auto &b = addr.bytes[i];
                if (b) {
                    return tl::nullopt;
                }
            }
            const auto &b = addr.bytes[last_address_i];
            if (!b || b > TTraits::static_precompiles) {
                return tl::nullopt;
            }
            return b - 1;
        }();

        return static_precompile_idx.transform(
            [](const unsigned idx) { return precompile_execs[idx]; });
    }
};

MONAD_EXECUTION_NAMESPACE_END