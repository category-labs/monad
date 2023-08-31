#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>

#include <evmc/evmc.hpp>

#include <tl/optional.hpp>

#include <boost/mp11/mpl_list.hpp>

#include <cstring>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <
    class TState, concepts::fork_traits<TState> TTraits, class TPrecompiles>
struct StaticPrecompiles
{
    using exec_func_t = evmc::Result (*)(evmc_message const &) noexcept;

    template <typename... Types>
    static constexpr auto
    construct_precompile_array(boost::mp11::mp_list<Types...>)
    {
        return std::array<exec_func_t, sizeof...(Types)>{Types::execute...};
    }

    static constexpr auto precompile_execs =
        construct_precompile_array(TPrecompiles{});

    static constexpr auto null{0x00_address};

    [[nodiscard]] static tl::optional<exec_func_t>
    static_precompile_exec_func(address_t const &addr) noexcept
    {
        auto const static_precompile_idx =
            [&]() -> tl::optional<unsigned const> {
            const auto last_address_i = sizeof(address_t) - 1u;

            if (std::memcmp(addr.bytes, &null, last_address_i)) {
                return tl::nullopt;
            }

            const auto &b = addr.bytes[last_address_i];
            if (!b || b > boost::mp11::mp_size<TPrecompiles>()) {
                return tl::nullopt;
            }
            return b - 1;
        }();

        return static_precompile_idx.transform(
            [](unsigned const idx) { return precompile_execs[idx]; });
    }
};

MONAD_EXECUTION_NAMESPACE_END
