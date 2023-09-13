#pragma once

#include <monad/config.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>

#include <monad/execution/ethereum/dao.hpp>

#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>

#include <monad/state2/state.hpp>

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
    struct paris;
    struct shanghai;

    using no_next_fork_t = shanghai;

    template <class TState>
    static constexpr uint256_t calculate_block_award(
        TState const &s, Block const &b, uint256_t const &reward,
        uint256_t const &ommer_reward)
    {
        return reward + ommer_reward * b.ommers.size() + s.gas_award();
    }

    static constexpr uint256_t calculate_ommer_award(
        Block const &b, uint256_t const &reward, uint64_t ommer_number)
    {
        auto const subtrahend = ((b.header.number - ommer_number) * reward) / 8;
        return reward - subtrahend;
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

        static constexpr uint64_t n_precompiles = 4;

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
        static constexpr void apply_block_award_impl(
            TState &s, Block const &b, uint256_t const &reward,
            uint256_t const &ommer_reward)
        {
            auto const miner_award =
                calculate_block_award(s, b, reward, ommer_reward);

            // reward block beneficiary, YP Eqn. 172
            s.apply_reward(b.header.beneficiary, miner_award);

            // reward ommers, YP Eqn. 175
            for (auto const &header : b.ommers) {
                s.apply_reward(
                    header.beneficiary,
                    calculate_ommer_award(b, reward, header.number));
            }
        }

        template <class TState>
        static constexpr void apply_block_award(TState &s, Block const &b)
        {
            apply_block_award_impl(s, b, block_reward, additional_ommer_reward);
        }

        template <class TState>
        static constexpr void apply_txn_award(
            TState &s, Transaction const &t, uint64_t base_gas_cost,
            uint64_t gas_used)
        {
            s.add_txn_award(uint256_t{gas_used} * gas_price(t, base_gas_cost));
        }

        template <class TBlockState, class TBlockCache>
        static constexpr void transfer_balance_dao(
            TBlockState &, Db &, TBlockCache const &, block_num_t const)
        {
        }

        static constexpr void validate_block(Block const &) {}

        template <typename TState>
        static constexpr void warm_coinbase(TState &, address_t const &)
        {
        }

        template <typename TState>
        static constexpr void process_withdrawal(
            TState &, std::optional<std::vector<Withdrawal>> const &)
        {
        }

        [[nodiscard]] static constexpr bool
        access_list_valid(Transaction::AccessList const &list)
        {
            return list.empty();
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

        template <class TBlockState, class TBlockCache>
        static constexpr void transfer_balance_dao(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            block_num_t const block_number)
        {
            state::State s{bs, db, block_cache};
            if (MONAD_UNLIKELY(
                    block_number == execution::dao::dao_block_number)) {
                for (auto const &addr : execution::dao::child_accounts) {
                    s.set_balance(
                        execution::dao::withdraw_account,
                        intx::be::load<uint256_t>(
                            s.get_balance(execution::dao::withdraw_account)) +
                            intx::be::load<uint256_t>(s.get_balance(addr)));
                    s.set_balance(addr, 0u);
                }

                MONAD_DEBUG_ASSERT(can_merge(bs.state, s.state_));
                merge(bs.state, s.state_);
            }
        }
    };

    struct tangerine_whistle : public dao_fork
    {
        using next_fork_t = spurious_dragon;

        static constexpr auto last_block_number = 2'674'999u;
        static constexpr evmc_revision rev = EVMC_TANGERINE_WHISTLE;

        template <class TBlockState, class TBlockCache>
        static constexpr void transfer_balance_dao(
            TBlockState &, Db &, TBlockCache const &, block_num_t const block)
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

        template <class TState>
        static constexpr void apply_block_award_impl(
            TState &s, Block const &b, uint256_t const &reward,
            uint256_t const &ommer_reward)
        {
            auto const miner_reward =
                calculate_block_award(s, b, reward, ommer_reward);

            // reward block beneficiary, YP Eqn. 172
            if (miner_reward) {
                s.apply_reward(b.header.beneficiary, miner_reward);
            }

            // reward ommers, YP Eqn. 175
            for (auto const &header : b.ommers) {
                auto const ommer_reward =
                    calculate_ommer_award(b, reward, header.number);
                if (ommer_reward) {
                    s.apply_reward(header.beneficiary, ommer_reward);
                }
            }
        }

        template <class TState>
        static constexpr void apply_block_award(TState &s, Block const &b)
        {
            apply_block_award_impl(s, b, block_reward, additional_ommer_reward);
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

        static constexpr uint64_t n_precompiles = 8;

        template <class TState>
        static constexpr void apply_block_award(TState &s, Block const &b)
        {
            apply_block_award_impl(s, b, block_reward, additional_ommer_reward);
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
            apply_block_award_impl(s, b, block_reward, additional_ommer_reward);
        }
    };

    struct istanbul : public constantinople_and_petersburg
    {
        using next_fork_t = berlin;

        static constexpr evmc_revision rev = EVMC_ISTANBUL;
        static constexpr auto last_block_number = 12'243'999u;

        static constexpr uint64_t n_precompiles = 9;

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

        // https://eips.ethereum.org/EIPS/eip-2930
        [[nodiscard]] static constexpr bool
        access_list_valid(Transaction::AccessList const &)
        {
            return true;
        }
    };

    struct london : public berlin
    {
        using next_fork_t = paris;

        static constexpr evmc_revision rev = EVMC_LONDON;
        static constexpr auto last_block_number = 15'537'393u;

        // https://eips.ethereum.org/EIPS/eip-3529
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

    struct paris : public london
    {
        using next_fork_t = shanghai;
        static constexpr evmc_revision rev = EVMC_PARIS;
        static constexpr auto last_block_number = 17'034'869u;

        // EIP-3675
        static constexpr uint256_t block_reward = 0;
        static constexpr uint256_t additional_ommer_reward = 0;

        template <class TState>
        static constexpr void apply_block_award(TState &s, Block const &b)
        {
            apply_block_award_impl(s, b, block_reward, additional_ommer_reward);
        }

        static constexpr void validate_block(Block const &b)
        {
            MONAD_DEBUG_ASSERT(b.header.ommers_hash == NULL_LIST_HASH);
            MONAD_DEBUG_ASSERT(b.header.difficulty == 0u);
            byte_string_fixed<8> empty{
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
            MONAD_DEBUG_ASSERT(b.header.nonce == empty);
            MONAD_DEBUG_ASSERT(b.ommers.size() == 0u);
            MONAD_DEBUG_ASSERT(b.header.extra_data.length() <= 32u);
        }
    };

    struct shanghai : public paris
    {
        using next_fork_t = no_next_fork_t;
        static constexpr evmc_revision rev = EVMC_SHANGHAI;
        static constexpr auto last_block_number =
            std::numeric_limits<uint64_t>::max();

        // EIP-3651
        template <class TState>
        static constexpr void
        warm_coinbase(TState &s, address_t const &beneficiary)
        {
            s.warm_coinbase(beneficiary);
        }

        // EIP-3860
        [[nodiscard]] static constexpr uint64_t
        g_extra_cost_init(Transaction const &t) noexcept
        {
            if (!t.to.has_value()) {
                return ((t.data.length() + 31u) / 32u) * 2u;
            }
            return 0u;
        }

        // EIP-3860
        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            if (!t.to.has_value()) {
                if (t.data.length() > 0xc000) {
                    return std::numeric_limits<uint64_t>::max();
                }
            }
            return g_txcreate(t) + 21'000u + g_data(t) +
                   g_access_and_storage(t) + g_extra_cost_init(t);
        }

        // EIP-4895
        template <typename TState>
        static constexpr void process_withdrawal(
            TState &s,
            std::optional<std::vector<Withdrawal>> const &withdrawals) noexcept
        {
            if (withdrawals.has_value()) {

                for (auto const &withdrawal : withdrawals.value()) {
                    s.set_balance(
                        withdrawal.recipient,
                        intx::be::load<uint256_t>(
                            s.get_balance(withdrawal.recipient)) +
                            uint256_t{withdrawal.amount} *
                                uint256_t{1'000'000'000u});
                }
            }
        }
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
    static_assert(boost::mp11::mp_size<all_forks_t>::value == 12);
}

MONAD_NAMESPACE_END
