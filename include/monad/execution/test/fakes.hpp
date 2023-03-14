#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <evmc/evmc.hpp>

#include <tl/expected.hpp>

#include <optional>
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
        uint64_t _refund{};
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

        void selfdestruct(address_t const &, address_t const &) noexcept {}

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

        uint64_t get_refund() const noexcept { return _refund; }

        void destruct_touched_dead() { _touched_dead = 0; }

        void destruct_suicides() { _suicides = 0; }

        void revert(){};

        void store_log(Receipt::Log &&l) { _logs.emplace_back(l); }

        std::vector<Receipt::Log> &logs() { return _logs; }
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
                evmc::result const &, Transaction const &,
                uint64_t const)
        {
            return _receipt;
        }

        [[nodiscard]] inline evmc::result call(evmc_message const &) noexcept
        {
            return evmc::result{_result};
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

    template <class TState>
    struct traits
    {
        static inline uint64_t _sd_refund{};
        static inline uint64_t block_number{};
        static inline uint64_t _intrinsic_gas{21'000u};
        static inline uint64_t _max_refund_quotient{2u};
        static inline bool _fail_store_contract{};
        static inline uint64_t _gas_creation_cost{};
        static inline uint64_t _create_address{};
        static inline auto intrinsic_gas(Transaction const &)
        {
            return _intrinsic_gas;
        }
        static inline auto starting_nonce() { return 1; }
        static inline auto max_refund_quotient()
        {
            return _max_refund_quotient;
        }
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

    static_assert(concepts::fork_traits<traits<State>, State>);
}

MONAD_EXECUTION_NAMESPACE_END
