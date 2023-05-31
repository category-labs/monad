#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>

#include <monad/execution/static_precompiles/big_number_add.hpp>
#include <monad/execution/static_precompiles/big_number_multiply.hpp>
#include <monad/execution/static_precompiles/big_number_pairing.hpp>
#include <monad/execution/static_precompiles/blake2f.hpp>
#include <monad/execution/static_precompiles/elliptic_curve_recover.hpp>
#include <monad/execution/static_precompiles/identity.hpp>
#include <monad/execution/static_precompiles/modular_exponentiation.hpp>
#include <monad/execution/static_precompiles/ripemd160_hash.hpp>
#include <monad/execution/static_precompiles/sha256_hash.hpp>

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

template <typename TState, concepts::fork_traits<TState> TTraits>
using frontier_static_precompiles_t = StaticPrecompiles<
    TState, TTraits, static_precompiles::EllipticCurveRecover<TState, TTraits>,
    static_precompiles::Sha256Hash<TState, TTraits>,
    static_precompiles::Ripemd160Hash<TState, TTraits>,
    static_precompiles::Identity<TState, TTraits>>;

template <typename TState, concepts::fork_traits<TState> TTraits>
using homestead_static_precompiles_t =
    frontier_static_precompiles_t<TState, TTraits>;

template <typename TState, concepts::fork_traits<TState> TTraits>
using spurious_dragon_static_precompiles_t =
    homestead_static_precompiles_t<TState, TTraits>;

template <typename TState, concepts::fork_traits<TState> TTraits>
using byzantium_static_precompiles_t = StaticPrecompiles<
    TState, TTraits, static_precompiles::EllipticCurveRecover<TState, TTraits>,
    static_precompiles::Sha256Hash<TState, TTraits>,
    static_precompiles::Ripemd160Hash<TState, TTraits>,
    static_precompiles::Identity<TState, TTraits>,
    static_precompiles::ModularExponentiation<TState, TTraits>,
    static_precompiles::BigNumberAdd<TState, TTraits>,
    static_precompiles::BigNumberMultiply<TState, TTraits>,
    static_precompiles::BigNumberPairing<TState, TTraits>>;

template <typename TState, concepts::fork_traits<TState> TTraits>
using istanbul_static_precompiles_t = StaticPrecompiles<
    TState, TTraits, static_precompiles::EllipticCurveRecover<TState, TTraits>,
    static_precompiles::Sha256Hash<TState, TTraits>,
    static_precompiles::Ripemd160Hash<TState, TTraits>,
    static_precompiles::Identity<TState, TTraits>,
    static_precompiles::ModularExponentiation<TState, TTraits>,
    static_precompiles::BigNumberAdd<TState, TTraits>,
    static_precompiles::BigNumberMultiply<TState, TTraits>,
    static_precompiles::BigNumberPairing<TState, TTraits>,
    static_precompiles::Blake2F<TState, TTraits>>;

template <typename TState, concepts::fork_traits<TState> TTraits>
using berlin_static_precompiles_t =
    istanbul_static_precompiles_t<TState, TTraits>;

template <typename TState, concepts::fork_traits<TState> TTraits>
using london_static_precompiles_t =
    berlin_static_precompiles_t<TState, TTraits>;

MONAD_EXECUTION_NAMESPACE_END