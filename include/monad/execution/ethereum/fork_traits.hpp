#pragma once

#include <monad/config.hpp>

#include <monad/core/concepts.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>

#include <monad/execution/ethereum/dao.hpp>
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
    struct dao_fork;
    struct tangerine_whistle;
    struct spurious_dragon;
    struct byzantium;
    struct constantinople_and_petersburg;
    struct istanbul;
    struct berlin;
    struct london;
    struct shanghai;

    using no_next_fork_t = shanghai;

    template <typename TFork, template <typename> typename... TPrecompiles>
    using type_list_t = boost::mp11::mp_list<TPrecompiles<TFork>...>;

    namespace contracts = execution::static_precompiles;

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
            constexpr auto word_size = sizeof(monad::bytes32_t);
            return (size + word_size - 1) / word_size * per_word() + base();
        }
    };

    template <class TState>
    static constexpr void apply_mining_award(
        TState &s, Block const &b, uint256_t const &reward,
        uint256_t const &ommer_reward)
    {
        // reward block beneficiary, YP Eqn. 172
        uint256_t const miner_reward = reward + ommer_reward * b.ommers.size();
        s.apply_block_reward(b.header.beneficiary, miner_reward);

        // reward ommers, YP Eqn. 175
        for (auto &i : b.ommers) {
            auto const subtrahend = ((b.header.number - i.number) * reward) / 8;
            s.apply_ommer_reward(i.beneficiary, reward - subtrahend);
        }
    }

    struct frontier
    {
        using next_fork_t = homestead;

        static constexpr evmc_revision rev = EVMC_FRONTIER;
        static constexpr auto last_block_number = 1'149'999u;
        static constexpr uint256_t block_reward =
            5'000'000'000'000'000'000; // YP Eqn. 176
        static constexpr uint256_t additional_ommer_reward =
            block_reward >> 5; // YP Eqn. 172, block reward / 32

        // YP Appendix E Eqn. 209
        using elliptic_curve_recover_gas_t = gas_required<3000, 0>;
        // YP Appendix E Eqn. 221
        using sha256_gas_t = gas_required<60, 12>;
        // YP Appendix E Eqn. 224
        using ripemd160_gas_t = gas_required<600, 120>;
        // YP Appendix E Eqn. 230
        using identity_gas_t = gas_required<15, 3>;

        using static_precompiles_t = type_list_t<
            frontier, contracts::EllipticCurveRecover, contracts::Sha256Hash,
            contracts::Ripemd160Hash, contracts::Identity>;
        static_assert(boost::mp11::mp_size<static_precompiles_t>() == 4);

        // YP, Eqn. 60, first summation
        [[nodiscard]] static constexpr uint64_t
        g_data(Transaction const &t) noexcept
        {
            auto const zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            auto const nonzeros = t.data.size() - static_cast<uint64_t>(zeros);
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
        static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            auto const deploy_cost =
                static_cast<int64_t>(result.output_size) * 200;
            result.create_address = a;

            if (result.gas_left < deploy_cost) {
                // From YP: "No code is deposited in the state if the gas
                // does not cover the additional per-byte contract deposit
                // fee, however, the value is still transferred and the
                // execution side- effects take place."
                s.set_code(a, {});
            }
            else {
                s.set_code(a, {result.output_data, result.output_size});
                result.gas_left -= deploy_cost;
            }
            return result;
        }

        static constexpr uint64_t
        gas_price(Transaction const &t, uint64_t const /*base_gas_price*/)
        {
            return t.gas_price;
        }

        template <class TState>
        static constexpr void apply_block_award(TState &s, Block const &b)
        {
            apply_mining_award(s, b, block_reward, additional_ommer_reward);
        }

        template <class TState>
        static constexpr void apply_txn_award(
            TState &s, Transaction const &t, uint64_t base_gas_cost,
            uint64_t gas_used)
        {
            s.add_txn_award(uint256_t{gas_used} * gas_price(t, base_gas_cost));
        }

        template <typename TState>
        static constexpr void transfer_balance_dao(TState &, block_num_t const)
        {
        }
    };

    struct homestead : public frontier
    {
        using next_fork_t = dao_fork;

        // https://eips.ethereum.org/EIPS/eip-2
        static constexpr evmc_revision rev = EVMC_HOMESTEAD;
        static constexpr auto last_block_number = 1'919'999u;

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
        static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            auto const deploy_cost =
                static_cast<int64_t>(result.output_size) * 200;

            if (result.gas_left < deploy_cost) {
                // EIP-2: If contract creation does not have enough gas to
                // pay for the final gas fee for adding the contract code to
                // the state, the contract creation fails (ie. goes
                // out-of-gas) rather than leaving an empty contract.
                //
                // TODO: make sure old initialization code does not get
                // committed to the database
                result.status_code = EVMC_OUT_OF_GAS;
                result.gas_left = 0;
            }
            else {
                result.create_address = a;
                result.gas_left -= deploy_cost;
                s.set_code(a, {result.output_data, result.output_size});
            }
            return result;
        }
    };

    struct dao_fork : public homestead
    {
        using next_fork_t = tangerine_whistle;
        static constexpr auto last_block_number = 2'462'999u;
        // EVMC revision for DAO should just be EVMC_HOMESTEAD

        template <typename TState>
        static constexpr void
        transfer_balance_dao(TState &s, block_num_t const block_number)
        {
            if (MONAD_UNLIKELY(
                    block_number == execution::dao::dao_block_number)) {
                auto change_set = s.get_new_changeset(0u);
                for (auto const &addr : execution::dao::child_accounts) {
                    change_set.set_balance(
                        execution::dao::withdraw_account,
                        intx::be::load<uint256_t>(change_set.get_balance(
                            execution::dao::withdraw_account)) +
                            intx::be::load<uint256_t>(
                                change_set.get_balance(addr)));
                    change_set.set_balance(addr, 0u);
                }

                // TODO: Workaround to get txn_id right for now. Ideally we want
                // to commit block changes all at once
                MONAD_DEBUG_ASSERT(
                    s.can_merge_changes(change_set) ==
                    TState::MergeStatus::WILL_SUCCEED);
                s.merge_changes(change_set);
                s.commit();
            }
        }
    };

    struct tangerine_whistle : public dao_fork
    {
        using next_fork_t = spurious_dragon;

        static constexpr auto last_block_number = 2'674'999u;
        static constexpr evmc_revision rev = EVMC_TANGERINE_WHISTLE;

        template <typename TState>
        static constexpr void transfer_balance_dao(TState &, block_num_t block)
        {
            MONAD_DEBUG_ASSERT(block > dao_fork::last_block_number);
        }
    };

    struct spurious_dragon : public tangerine_whistle
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

        template <class TState>
        [[nodiscard]] static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            // EIP-170
            if (result.output_size > 0x6000) {
                return evmc::Result{EVMC_OUT_OF_GAS};
            }
            return homestead::deploy_contract_code(s, a, std::move(result));
        }
    };

    struct byzantium : public spurious_dragon
    {
        using next_fork_t = constantinople_and_petersburg;

        static constexpr evmc_revision rev = EVMC_BYZANTIUM;
        static constexpr auto last_block_number = 7'279'999u;
        static constexpr uint256_t block_reward =
            3'000'000'000'000'000'000; // YP Eqn. 176, EIP-649
        static constexpr uint256_t additional_ommer_reward =
            block_reward >> 5; // YP Eqn. 172, block reward / 32

        // YP Appendix E Eq 279
        using bn_add_gas_t = gas_required<500, 0>;
        // YP Appendix E Eq 285
        using bn_mul_gas_t = gas_required<40'000, 0>;

        // YP Appendix E Eq 270
        static constexpr int64_t bn_pairing_base_gas = 100'000;
        static constexpr int64_t bn_pairing_per_point_gas = 80'000;

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
        static constexpr void apply_block_award(TState &s, Block const &b)
        {
            apply_mining_award(s, b, block_reward, additional_ommer_reward);
        }
    };

    // EIP-1716 petersburg and constantinople forks are activated at the same
    // block on mainnet
    struct constantinople_and_petersburg : public byzantium
    {
        using next_fork_t = istanbul;

        static constexpr evmc_revision rev = EVMC_PETERSBURG;
        static constexpr auto last_block_number = 9'068'999;
        static constexpr uint256_t block_reward =
            2'000'000'000'000'000'000; // YP Eqn. 176, EIP-1234
        static constexpr uint256_t additional_ommer_reward =
            block_reward >> 5; // YP Eqn. 172, block reward / 32

        template <class TState>
        static constexpr void apply_block_award(TState &s, Block const &b)
        {
            apply_mining_award(s, b, block_reward, additional_ommer_reward);
        }
    };

    struct istanbul : public constantinople_and_petersburg
    {
        using next_fork_t = berlin;

        static constexpr evmc_revision rev = EVMC_ISTANBUL;
        static constexpr auto last_block_number = 12'243'999u;

        // YP Appendix E Eq 279
        using bn_add_gas_t = gas_required<150, 0>;
        // YP Appendix E Eq 285
        using bn_mul_gas_t = gas_required<6'000, 0>;

        // YP Appendix E Eq 270
        static constexpr int64_t bn_pairing_base_gas = 45'000;
        static constexpr int64_t bn_pairing_per_point_gas = 34'000;

        template <typename TList>
        using switch_fork_t = boost::mp11::mp_replace_front<TList, istanbul>;

        using static_precompiles_t = boost::mp11::mp_append<
            boost::mp11::mp_transform<
                switch_fork_t,
                constantinople_and_petersburg::static_precompiles_t>,
            type_list_t<istanbul, contracts::Blake2F>>;
        static_assert(boost::mp11::mp_size<static_precompiles_t>() == 9);

        // https://eips.ethereum.org/EIPS/eip-2028
        [[nodiscard]] static constexpr uint64_t
        g_data(Transaction const &t) noexcept
        {
            auto const zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            auto const nonzeros = t.data.size() - static_cast<uint64_t>(zeros);
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

        template <typename TList>
        using switch_fork_t = boost::mp11::mp_replace_front<TList, berlin>;

        using static_precompiles_t = boost::mp11::mp_transform<
            switch_fork_t, istanbul::static_precompiles_t>;
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
        using next_fork_t = shanghai;

        static constexpr evmc_revision rev = EVMC_LONDON;
        static constexpr auto last_block_number = 15'537'393u;

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
        [[nodiscard]] static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            if (result.output_size > 0 && result.output_data[0] == 0xef) {
                return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
            }
            return berlin::deploy_contract_code(s, a, std::move(result));
        }

        // https://eips.ethereum.org/EIPS/eip-1559
        static constexpr uint64_t
        gas_price(Transaction const &t, uint64_t const base_gas_price)
        {
            if (t.type == Transaction::Type::eip1559) {
                MONAD_DEBUG_ASSERT(
                    (base_gas_price + t.priority_fee) <= t.gas_price);
                return base_gas_price + t.priority_fee;
            }
            MONAD_DEBUG_ASSERT(t.gas_price >= base_gas_price);
            return t.gas_price;
        }

        // https://eips.ethereum.org/EIPS/eip-1559
        static constexpr uint64_t
        miner_priority_gas_cost(Transaction const &t, uint64_t base_gas_price)
        {
            if (t.type == Transaction::Type::eip1559) {
                return t.priority_fee;
            }
            return t.gas_price - base_gas_price;
        }

        template <class TState>
        static constexpr void apply_txn_award(
            TState &s, Transaction const &t, uint64_t base_gas_cost,
            uint64_t gas_used)
        {
            s.add_txn_award(uint256_t{
                gas_used * miner_priority_gas_cost(t, base_gas_cost)});
        }
    };

    struct shanghai : public london
    {
        using next_fork_t = no_next_fork_t;
        static constexpr evmc_revision rev = EVMC_SHANGHAI;
        static constexpr auto last_block_number =
            std::numeric_limits<uint64_t>::max();
    };

    namespace detail
    {
        template <typename T>
        constexpr auto Traverse()
        {
            if constexpr (requires { typename T::next_fork_t; }) {
                return boost::mp11::mp_push_front<
                    decltype(Traverse<typename T::next_fork_t>()),
                    T>{};
            }
            else {
                return boost::mp11::mp_list<T>{};
            }
        }

        template <>
        constexpr auto Traverse<monad::fork_traits::no_next_fork_t>()
        {
            return boost::mp11::mp_list<monad::fork_traits::no_next_fork_t>{};
        }
    }

    using all_forks_t =
        decltype(detail::Traverse<monad::fork_traits::frontier>());
    static_assert(boost::mp11::mp_size<all_forks_t>::value == 11);
}

MONAD_NAMESPACE_END
