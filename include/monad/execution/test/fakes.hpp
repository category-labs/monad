#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/static_precompiles.hpp>

#include <evmc/evmc.hpp>

#include <tl/expected.hpp>

#include <unordered_map>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace fake
{
    inline evmc_vm *get_fake_evmc()
    {
        return NULL;
    }

    // Simple fake State
    struct State
    {
        std::unordered_map<address_t, Account> _map{};
        uint64_t _selfdestructs{};
        uint64_t _touched_dead{};
        uint64_t _suicides{};
        int _current_txn{};
        bool _applied_state{};
        std::vector<Receipt::Log> _logs{};

        [[nodiscard]] bool account_exists(address_t const &) { return true; }

        [[nodiscard]] bytes32_t
        get_storage(address_t const &, bytes32_t const &) const noexcept
        {
            return {};
        }

        [[nodiscard]] evmc_storage_status set_storage(
            address_t const &, bytes32_t const &, bytes32_t const &) noexcept
        {
            return {};
        }

        void create_contract(address_t const &) noexcept {}

        [[nodiscard]] bytes32_t
        get_balance(address_t const &address) const noexcept
        {
            return intx::be::store<bytes32_t>(_map.at(address).balance);
        }

        [[nodiscard]] size_t get_code_size(address_t const &) const noexcept
        {
            return 0u;
        }

        [[nodiscard]] size_t
        copy_code(address_t const &, size_t, uint8_t *, size_t) const noexcept
        {
            return 0u;
        }

        [[nodiscard]] bytes32_t
        get_code_hash(address_t const &address) const noexcept
        {
            return _map.at(address).code_hash;
        }

        bool selfdestruct(address_t const &, address_t const &) noexcept
        {
            return true;
        }

        evmc_access_status access_account(address_t const &) noexcept
        {
            return {};
        }
        evmc_access_status
        access_storage(address_t const &, bytes32_t const &) noexcept
        {
            return {};
        }

        [[nodiscard]] bytes32_t get_block_hash(int64_t) { return {}; }

        // non-evmc interface
        void set_balance(address_t const &address, uint256_t new_balance)
        {
            _map[address].balance = new_balance;
        }
        [[nodiscard]] auto get_nonce(address_t const &address) const noexcept
        {
            return _map.at(address).nonce;
        }
        void set_nonce(address_t const &address, uint64_t nonce) noexcept
        {
            _map[address].nonce = nonce;
        }

        void set_code(address_t const &, byte_string const &) {}

        uint64_t total_selfdestructs() const noexcept { return _selfdestructs; }

        void destruct_touched_dead() { _touched_dead = 0; }

        void destruct_suicides() { _suicides = 0; }

        void revert(){};

        void store_log(Receipt::Log &&l) { _logs.emplace_back(l); }

        std::vector<Receipt::Log> &logs() { return _logs; }

        inline bool apply_state(State const &) { return _applied_state; }

        inline int current_txn() { return _current_txn; }

        inline State get_copy() { return State(*this); }
    };

    struct EvmHost
    {
        evmc_result _result{};
        Receipt _receipt{};

        [[nodiscard]] static constexpr inline evmc_message
        make_msg_from_txn(Transaction const &)
        {
            return {.kind = EVMC_CALL};
        };

        [[nodiscard]] constexpr inline Receipt make_receipt_from_result(
            evmc::Result const &, Transaction const &, uint64_t const)
        {
            return _receipt;
        }

        [[nodiscard]] inline evmc::Result call(evmc_message const &) noexcept
        {
            return evmc::Result{_result};
        }
    };

    struct Evm
    {
        using new_address_t = tl::expected<address_t, evmc_result>;
        using unexpected_t = tl::unexpected<evmc_result>;

        new_address_t _result{};
        evmc_result _e_result{};

        [[nodiscard]] tl::expected<address_t, evmc_result>
        make_account_address(evmc_message const &) noexcept
        {
            return _result;
        }
        [[nodiscard]] evmc_result transfer_call_balances(evmc_message const &)
        {
            return _e_result;
        }
    };

    namespace traits
    {
        template <class TState>
        struct alpha
        {
            using next_fork_t = alpha;
            static inline uint64_t _sd_refund{};
            static inline uint64_t last_block_number{
                std::numeric_limits<uint64_t>::max()};
            static inline uint64_t static_precompiles{1};
            static inline uint64_t _intrinsic_gas{21'000u};
            static inline uint64_t _max_refund_quotient{2u};
            static inline bool _fail_store_contract{};
            static inline uint64_t _gas_creation_cost{};
            static inline uint64_t _create_address{};
            static inline uint64_t _echo_gas_cost{10};
            static inline auto intrinsic_gas(Transaction const &)
            {
                return _intrinsic_gas;
            }
            static inline auto starting_nonce() { return 1u; }
            static inline auto max_refund_quotient()
            {
                return _max_refund_quotient;
            }
            static inline auto echo_gas_cost() { return _echo_gas_cost; }
            static inline auto get_selfdestruct_refund(TState const &)
            {
                return _sd_refund;
            }
            static inline void destruct_touched_dead(TState &s)
            {
                s.destruct_touched_dead();
            }
            static constexpr inline bool
            store_contract_code(TState &, address_t const &a, evmc_result &r)
            {
                r.gas_left -= _gas_creation_cost;
                if (!_fail_store_contract) {
                    r.create_address = a;
                }
                return _fail_store_contract;
            }
        };

        template <class TState>
        struct beta : public alpha<TState>
        {
            using next_fork_t = beta;
            static inline uint64_t last_block_number{
                std::numeric_limits<uint64_t>::max()};
            static inline uint64_t static_precompiles{2};
            static inline uint64_t _echo_gas_cost{15};
            static inline auto echo_gas_cost() { return _echo_gas_cost; }
        };

        static_assert(concepts::fork_traits<alpha<State>, State>);
        static_assert(concepts::fork_traits<beta<State>, State>);
    }

    namespace static_precompiles
    {
        template <class TState, concepts::fork_traits<TState> TTraits>
        struct Echo
        {
            static evmc_result execute(const evmc_message &m) noexcept
            {
                const int64_t gas =
                    (const int64_t)(m.input_size * TTraits::echo_gas_cost());
                if (m.gas < gas) {
                    return {.status_code = EVMC_OUT_OF_GAS};
                }
                unsigned char *output_data =
                    (unsigned char *)std::malloc(m.input_size);
                std::memcpy(output_data, m.input_data, m.input_size);
                return {
                    .status_code = EVMC_SUCCESS,
                    .gas_left = m.gas - gas,
                    .output_data = output_data,
                    .output_size = m.input_size,
                    .release = [](const evmc_result *result) {
                        std::free((unsigned char *)result->output_data);
                    }};
            }
        };

        template <class TState, concepts::fork_traits<TState> TTraits>
        struct OneHundredGas
        {
            static evmc_result execute(const evmc_message &m) noexcept
            {
                const int64_t gas = 100;
                if (m.gas < gas) {
                    return {.status_code = EVMC_OUT_OF_GAS};
                }
                return {
                    .status_code = EVMC_SUCCESS,
                    .gas_left = m.gas - gas,
                    .output_size = 0u};
            }
        };
    }
}

MONAD_EXECUTION_NAMESPACE_END