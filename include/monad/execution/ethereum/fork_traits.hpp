#pragma once

#include <monad/config.hpp>

#include <monad/core/concepts.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/ethereum/static_precompiles/blake2f.hpp>
#include <monad/execution/ethereum/static_precompiles/bn_add.hpp>
#include <monad/execution/ethereum/static_precompiles/bn_multiply.hpp>
#include <monad/execution/ethereum/static_precompiles/bn_pairing.hpp>
#include <monad/execution/ethereum/static_precompiles/elliptic_curve_recover.hpp>
#include <monad/execution/ethereum/static_precompiles/identity.hpp>
#include <monad/execution/ethereum/static_precompiles/modular_exponentiation.hpp>
#include <monad/execution/ethereum/static_precompiles/ripemd160_hash.hpp>
#include <monad/execution/ethereum/static_precompiles/sha256_hash.hpp>

#include <monad/db/block_db.hpp>

#include <evmc/evmc.h>

#include <algorithm>

#include <boost/mp11/mpl_list.hpp>

MONAD_NAMESPACE_BEGIN

// https://ethereum.org/en/history/
namespace fork_traits
{
    struct frontier;
    struct homestead;
    struct spurious_dragon;
    struct byzantium;
    struct istanbul;
    struct berlin;
    struct london;

    using no_next_fork_t = london;

    template <typename TFork, template <typename> typename... TPrecompiles>
    using type_list_t = boost::mp11::mp_list<TPrecompiles<TFork>...>;

    namespace contracts = execution::ethereum::static_precompiles;

    /**
     * Gas cost for many precompiles is computed as Base + PerWord * N
     * where N is the number of 32-bit words used by the input
     * @tparam Base
     * @tparam PerWord
     * NOTE: Base and PerWord are signed integers to be more compatible with
     * evmc types
     */
    template <int64_t BaseCost, int64_t PerWordCost>
    struct gas_required
    {
        static_assert(BaseCost >= 0);
        static_assert(PerWordCost >= 0);
        using integer_type = int64_t;
        using base = std::integral_constant<int64_t, BaseCost>;
        using per_word = std::integral_constant<int64_t, PerWordCost>;

        /**
         * Implements the generic form of YP Appendix E Eq 221
         * @param size of input message in bytes
         * @return the total gas cost
         */
        static constexpr int64_t compute(size_t size)
        {
            auto constexpr word_size = sizeof(monad::bytes32_t);
            return (size + word_size - 1) / word_size * per_word() + base();
        }
    };

    struct frontier
    {
        using next_fork_t = homestead;

        static constexpr evmc_revision rev = EVMC_FRONTIER;
        static constexpr auto last_block_number = 1'149'999u;

        // YP Appendix E Eq 209
        using elliptic_curve_recover_gas_t = gas_required<3000, 0>;
        // YP Appendix E Eq 221
        using sha256_gas_t = gas_required<60, 12>;
        // YP Appendix E Eq 224
        using ripemd160_gas_t = gas_required<600, 120>;
        // YP Appendix E Eq 230
        using identity_gas_t = gas_required<15, 3>;

        using static_precompiles_t = type_list_t<
            frontier, contracts::EllipticCurveRecover, contracts::Sha256Hash,
            contracts::Ripemd160Hash, contracts::Identity>;
        static_assert(boost::mp11::mp_size<static_precompiles_t>() == 4);

        // YP, Eqn. 60, first summation
        [[nodiscard]] static constexpr uint64_t
        g_data(Transaction const &t) noexcept
        {
            const auto zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            const auto nonzeros = t.data.size() - static_cast<uint64_t>(zeros);
            return static_cast<uint64_t>(zeros) * 4u + nonzeros * 68u;
        }

        // YP, section 6.2, Eqn. 60
        [[nodiscard]] static constexpr uint64_t
        intrinsic_gas(Transaction const &t) noexcept
        {
            return 21'000 + g_data(t);
        }

        [[nodiscard]] static constexpr auto starting_nonce() noexcept
        {
            return 0u;
        }

        template <class TState>
        [[nodiscard]] static constexpr uint64_t
        get_selfdestruct_refund(TState const &s) noexcept
        {
            return s.total_selfdestructs() * 24'000;
        }

        [[nodiscard]] static constexpr uint64_t max_refund_quotient() noexcept
        {
            return 2u;
        }

        template <class TState>
        static constexpr void destruct_touched_dead(TState &) noexcept
        {
        }

        template <class TState>
        static constexpr bool enough_gas_to_store_code(
            TState &s, address_t const &a, evmc::Result &r) noexcept
        {
            auto const deploy_cost = r.output_size * 200u;
            if (static_cast<uint64_t>(r.gas_left) >= deploy_cost) {
                s.set_code(a, {r.output_data, r.output_size});
                r.gas_left -= deploy_cost;
                r.create_address = a;
                return true;
            }
            return false;
        }
        template <class TState>
        [[nodiscard]] static constexpr bool store_contract_code(
            TState &s, address_t const &a, evmc::Result &r) noexcept
        {
            if (r.status_code == EVMC_SUCCESS) {
                enough_gas_to_store_code(s, a, r);
            }
            else {
                r.gas_left = 0;
            }
            return true;
        }
    };

    struct homestead : public frontier
    {
        using next_fork_t = spurious_dragon;

        // https://eips.ethereum.org/EIPS/eip-2
        static constexpr evmc_revision rev = EVMC_HOMESTEAD;
        static constexpr auto last_block_number = 2'674'999u;

        [[nodiscard]] static constexpr auto
        g_txcreate(Transaction const &t) noexcept
        {
            if (!t.to.has_value()) {
                return 32'000u;
            }
            return 0u;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t);
        }

        template <class TState>
        [[nodiscard]] static constexpr bool store_contract_code(
            TState &s, address_t const &a, evmc::Result &r) noexcept
        {
            if (r.status_code == EVMC_SUCCESS) {
                if (!enough_gas_to_store_code(s, a, r)) {
                    r.status_code = EVMC_OUT_OF_GAS;
                    r.gas_left = 0;
                    return false;
                }
            }
            else {
                r.gas_left = 0;
                return false;
            }
            return true;
        }
    };

    // dao - 1'920'000
    // tangerine_whistle - 2'463'000

    struct spurious_dragon : homestead
    {
        using next_fork_t = byzantium;

        static constexpr evmc_revision rev = EVMC_SPURIOUS_DRAGON;
        static constexpr auto last_block_number = 4'369'999u;

        // https://eips.ethereum.org/EIPS/eip-161
        [[nodiscard]] static constexpr auto starting_nonce() noexcept
        {
            return 1u;
        }

        template <class TState>
        static constexpr void destruct_touched_dead(TState &s) noexcept
        {
            s.destruct_touched_dead();
        }

        static constexpr bool contract_too_big(evmc::Result &r) noexcept
        {
            // EIP-170
            if (r.output_size > 0x6000) {
                r.status_code = EVMC_OUT_OF_GAS;
                r.gas_left = 0;
                return true;
            }

            return false;
        }

        template <class TState>
        [[nodiscard]] static constexpr bool store_contract_code(
            TState &s, address_t const &a, evmc::Result &r) noexcept
        {
            if (contract_too_big(r)) {
                return false;
            }

            return homestead::store_contract_code(s, a, r);
        }
    };

    struct byzantium : spurious_dragon
    {
        using next_fork_t = istanbul;

        static constexpr evmc_revision rev = EVMC_BYZANTIUM;
        static constexpr auto last_block_number = 9'068'999u;

        // YP Appendix E Eq 279
        using bn_add_gas_t = gas_required<500, 0>;
        template <typename TList>
        using switch_fork_t = boost::mp11::mp_replace_front<TList, byzantium>;

        using static_precompiles_t = boost::mp11::mp_append<
            boost::mp11::mp_transform<
                switch_fork_t, homestead::static_precompiles_t>,
            type_list_t<
                byzantium, contracts::ModularExponentiation, contracts::BNAdd,
                contracts::BNMultiply, contracts::BNPairing>>;

        static_assert(boost::mp11::mp_size<static_precompiles_t>() == 8);

        template <class TState>
        [[nodiscard]] static constexpr bool store_contract_code(
            TState &s, address_t const &a, evmc::Result &r) noexcept
        {
            if (contract_too_big(r)) {
                return false;
            }

            if (r.status_code == EVMC_SUCCESS) {
                if (!enough_gas_to_store_code(s, a, r)) {
                    r.status_code = EVMC_OUT_OF_GAS;
                    r.gas_left = 0;
                    return false;
                }
                return true;
            }
            // EIP-140 - support remaining gas with REVERT
            else if (r.status_code != EVMC_REVERT) {
                r.gas_left = 0;
            }

            return false;
        }
    };
    // constantinople - 7'280'000

    struct istanbul : public byzantium // constantinople
    {
        using next_fork_t = berlin;

        static constexpr evmc_revision rev = EVMC_ISTANBUL;
        static constexpr auto last_block_number = 12'243'999u;

        using static_precompiles_t = type_list_t<
            istanbul, contracts::EllipticCurveRecover, contracts::Sha256Hash,
            contracts::Ripemd160Hash, contracts::Identity,
            contracts::ModularExponentiation, contracts::BNAdd,
            contracts::BNMultiply, contracts::BNPairing, contracts::Blake2F>;
        static_assert(boost::mp11::mp_size<static_precompiles_t>() == 9);

        // https://eips.ethereum.org/EIPS/eip-2028
        [[nodiscard]] static constexpr uint64_t
        g_data(Transaction const &t) noexcept
        {
            const auto zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            const auto nonzeros = t.data.size() - static_cast<uint64_t>(zeros);
            return static_cast<uint64_t>(zeros) * 4u + nonzeros * 16u;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t);
        }
    };

    // muir_glacier - 9'200'000

    struct berlin : public istanbul
    {
        using next_fork_t = london;

        static constexpr evmc_revision rev = EVMC_BERLIN;
        static constexpr auto last_block_number = 12'964'999u;

        using static_precompiles_t = type_list_t<
            berlin, contracts::EllipticCurveRecover, contracts::Sha256Hash,
            contracts::Ripemd160Hash, contracts::Identity,
            contracts::ModularExponentiation, contracts::BNAdd,
            contracts::BNMultiply, contracts::BNPairing, contracts::Blake2F>;
        static_assert(boost::mp11::mp_size<static_precompiles_t>() == 9);

        // https://eips.ethereum.org/EIPS/eip-2930
        [[nodiscard]] static constexpr auto
        g_access_and_storage(Transaction const &t) noexcept
        {
            uint64_t g = t.access_list.size() * 2'400u;
            for (auto &i : t.access_list) {
                g += i.keys.size() * 1'900u;
            }
            return g;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t) +
                   g_access_and_storage(t);
        }
    };

    struct london : public berlin
    {
        using next_fork_t = no_next_fork_t;

        static constexpr evmc_revision rev = EVMC_LONDON;
        static constexpr auto last_block_number =
            std::numeric_limits<uint64_t>::max();

        // https://eips.ethereum.org/EIPS/eip-3529
        template <class TState>
        [[nodiscard]] static constexpr uint64_t
        get_selfdestruct_refund(TState const &) noexcept
        {
            return 0u;
        }

        [[nodiscard]] static constexpr uint64_t max_refund_quotient() noexcept
        {
            return 5u;
        }

        // https://eips.ethereum.org/EIPS/eip-3541
        template <class TState>
        [[nodiscard]] static constexpr bool store_contract_code(
            TState &s, address_t const &a, evmc::Result &r) noexcept
        {
            if (r.output_size > 0 && r.output_data[0] == 0xef) {
                r.status_code = EVMC_CONTRACT_VALIDATION_FAILURE;
                r.gas_left = 0;
                return false;
            }
            return berlin::store_contract_code(s, a, r);
        }
    };

    // paris - 15'537'394
}

MONAD_NAMESPACE_END
