#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/static_precompiles.hpp>

#include <monad/state/concepts.hpp>
#include <monad/state/state_changes.hpp>

#include <evmc/evmc.hpp>

#include <tl/expected.hpp>

#include <unordered_map>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace fake
{
    struct Db
    {
        void create(address_t const &, Account const &) const noexcept
        {
            return;
        }
        void commit(state::changeset auto const &) const noexcept { return; }
        bytes32_t root_hash() const noexcept { return {}; }
    };

    struct AccountState
    {
        Db db_;
    };

    struct State
    {
        struct WorkingCopy
        {
            std::unordered_map<address_t, Account> _accounts{};
            std::unordered_map<address_t, byte_string> _code{};

            std::vector<Receipt::Log> _logs{};
            unsigned int _txn_id{};
            uint64_t _selfdestructs{};
            uint64_t _touched_dead{};
            uint64_t _suicides{};

            WorkingCopy() = default;

            WorkingCopy(unsigned int id)
                : _txn_id{id}
            {
            }

            unsigned int txn_id() const noexcept { return _txn_id; }

            void create_account(address_t const &) noexcept {}

            // EVMC Host Interface
            [[nodiscard]] bool account_exists(address_t const &a)
            {
                return _accounts.contains(a);
            }

            // EVMC Host Interface
            evmc_access_status access_account(address_t const &) noexcept
            {
                return {};
            }

            // EVMC Host Interface
            [[nodiscard]] bytes32_t
            get_balance(address_t const &address) const noexcept
            {
                return intx::be::store<bytes32_t>(
                    _accounts.at(address).balance);
            }

            void set_balance(address_t const &address, uint256_t new_balance)
            {
                _accounts[address].balance = new_balance;
            }

            [[nodiscard]] auto
            get_nonce(address_t const &address) const noexcept
            {
                return _accounts.at(address).nonce;
            }

            void set_nonce(address_t const &address, uint64_t nonce) noexcept
            {
                _accounts[address].nonce = nonce;
            }

            // EVMV Host Interface
            [[nodiscard]] bytes32_t
            get_code_hash(address_t const &address) const noexcept
            {
                return _accounts.at(address).code_hash;
            }

            [[nodiscard]] bool
            selfdestruct(address_t const &, address_t const &) noexcept
            {
                return true;
            }

            void destruct_suicides() { _suicides = 0; }

            void destruct_touched_dead() { _touched_dead = 0; }

            uint64_t total_selfdestructs() const noexcept
            {
                return _selfdestructs;
            }

            // EVMC Host Interface
            evmc_access_status
            access_storage(address_t const &, bytes32_t const &) noexcept
            {
                return {};
            }

            // EVMC Host Interface
            [[nodiscard]] bytes32_t
            get_storage(address_t const &, bytes32_t const &) const noexcept
            {
                return {};
            }

            // EVMC Host Interface
            [[nodiscard]] evmc_storage_status set_storage(
                address_t const &, bytes32_t const &,
                bytes32_t const &) noexcept
            {
                return {};
            }

            void set_code(address_t const &, byte_string const &) {}

            // EVMC Host Interface
            [[nodiscard]] size_t get_code_size(address_t const &) const noexcept
            {
                return 0u;
            }

            // EVMC Host Interface
            [[nodiscard]] size_t copy_code(
                address_t const &, size_t, uint8_t *, size_t) const noexcept
            {
                return 0u;
            }

            [[nodiscard]] byte_string_view
            get_code(address_t const &a) const noexcept
            {
                return {_code.at(a)};
            }

            void revert() noexcept { _accounts.clear(); }

            [[nodiscard]] bytes32_t get_block_hash(int64_t) const noexcept
            {
                return {};
            }

            void store_log(Receipt::Log &&l) { _logs.emplace_back(l); }

            std::vector<Receipt::Log> &logs() { return _logs; }
        };

        enum class MergeStatus
        {
            WILL_SUCCEED,
            TRY_LATER,
            COLLISION_DETECTED,
        };

        std::unordered_map<address_t, uint256_t> _block_reward{};

        void apply_reward(address_t const &a, uint256_t const &r)
        {
            _block_reward.insert({a, r});
        }

        // Had to name this variable using post_ because we access it directly
        AccountState accounts_{};

        unsigned int _current_txn{};

        MergeStatus _merge_status{MergeStatus::TRY_LATER};

        unsigned int current_txn() { return _current_txn; }

        WorkingCopy get_working_copy(unsigned int id)
        {
            return WorkingCopy(id);
        }

        MergeStatus can_merge_changes(WorkingCopy const &)
        {
            return _merge_status;
        }

        void merge_changes(WorkingCopy &) { return; }

        void commit() const noexcept { return; }

        [[nodiscard]] bytes32_t get_state_hash() const { return {}; }
    };

    template <class TState, concepts::fork_traits<TState> TTraits, class TEvm>
    struct EvmHost
    {
        evmc_result _result{};
        Receipt _receipt{};

        EvmHost() = default;

        EvmHost(BlockHeader const &, Transaction const &, TState &) noexcept {}

        [[nodiscard]] static constexpr inline evmc_message
        make_msg_from_txn(Transaction const &)
        {
            return {.kind = EVMC_CALL};
        };

        [[nodiscard]] constexpr inline Receipt make_receipt_from_result(
            evmc_status_code, Transaction const &, uint64_t const)
        {
            return _receipt;
        }

        [[nodiscard]] virtual evmc::Result call(evmc_message const &) noexcept
        {
            return evmc::Result{_result};
        }

        evmc_host_context *to_context() { return nullptr; }
        evmc_host_interface &get_interface()
        {
            return *reinterpret_cast<evmc_host_interface *>(this);
        }
    };

    template <
        class TState, concepts::fork_traits<TState> TTraits,
        class TStaticPrecompiles, class TInterpreter>
    struct Evm
    {
        using new_address_t = tl::expected<address_t, evmc_result>;
        using unexpected_t = tl::unexpected<evmc_result>;

        [[nodiscard]] static tl::expected<address_t, evmc_result>
        make_account_address(evmc_message const &) noexcept
        {
            return new_address_t{};
        }

        [[nodiscard]] static evmc_result
        transfer_call_balances(evmc_message const &)
        {
            return evmc_result{};
        }

        template <class TEvmHost>
        [[nodiscard]] static evmc::Result
        call_evm(TEvmHost *, TState &, evmc_message const &) noexcept
        {
            return evmc::Result{};
        }

        template <class TEvmHost>
        [[nodiscard]] static evmc::Result create_contract_account(
            TEvmHost *, TState &, evmc_message const &) noexcept
        {
            return evmc::Result{};
        }
    };

    namespace static_precompiles
    {
        template <typename>
        struct Echo;
        struct OneHundredGas;
    }

    struct Interpreter
    {
        static inline evmc::Result _result{};

        template <class TEvmHost, class TState>
        static evmc::Result execute(TEvmHost *, TState &, evmc_message const &)
        {
            return std::move(_result);
        }
    };

    namespace traits
    {
        template <class TState>
        struct alpha
        {
            using next_fork_t = alpha;

            static constexpr evmc_revision rev = EVMC_FRONTIER;
            static inline uint64_t _sd_refund{};
            static inline uint64_t last_block_number{
                std::numeric_limits<uint64_t>::max()};
            using static_precompiles_t =
                boost::mp11::mp_list<static_precompiles::Echo<alpha>>;
            static inline uint64_t _intrinsic_gas{21'000u};
            static inline uint64_t _max_refund_quotient{2u};
            static inline bool _success_store_contract{};
            static inline uint64_t _gas_creation_cost{};
            static inline uint64_t _create_address{};
            static constexpr uint64_t _echo_gas_cost{10};
            static constexpr void apply_block_award(TState &, Block const &) {}
            static auto intrinsic_gas(Transaction const &)
            {
                return _intrinsic_gas;
            }
            static auto starting_nonce() { return 1u; }
            static auto max_refund_quotient() { return _max_refund_quotient; }
            static consteval uint64_t echo_gas_cost() { return _echo_gas_cost; }
            static auto get_selfdestruct_refund(TState const &)
            {
                return _sd_refund;
            }
            static void destruct_touched_dead(TState &s)
            {
                s.destruct_touched_dead();
            }
            static constexpr bool
            store_contract_code(TState &, address_t const &a, evmc::Result &r)
            {
                r.gas_left -= _gas_creation_cost;
                if (_success_store_contract) {
                    r.create_address = a;
                }
                return _success_store_contract;
            }
        };

        template <class TState>
        struct beta : public alpha<TState>
        {
            using next_fork_t = beta;

            static constexpr evmc_revision rev = EVMC_HOMESTEAD;
            static inline uint64_t last_block_number{
                std::numeric_limits<uint64_t>::max()};
            using static_precompiles_t = boost::mp11::mp_list<
                static_precompiles::Echo<beta>,
                static_precompiles::OneHundredGas>;

            static constexpr uint64_t _echo_gas_cost{15};
            static consteval uint64_t echo_gas_cost() { return _echo_gas_cost; }
        };
    }

    namespace static_precompiles
    {
        template <typename T>
        struct Echo
        {
            static evmc::Result execute(const evmc_message &m) noexcept
            {
                const int64_t gas =
                    (const int64_t)(m.input_size * T::echo_gas_cost());
                if (m.gas < gas) {
                    return evmc::Result{
                        evmc_result{.status_code = EVMC_OUT_OF_GAS}};
                }
                unsigned char *output_data =
                    (unsigned char *)std::malloc(m.input_size);
                std::memcpy(output_data, m.input_data, m.input_size);
                return evmc::Result{evmc_result{
                    .status_code = EVMC_SUCCESS,
                    .gas_left = m.gas - gas,
                    .output_data = output_data,
                    .output_size = m.input_size,
                    .release = [](const evmc_result *result) {
                        std::free((unsigned char *)result->output_data);
                    }}};
            }
        };

        struct OneHundredGas
        {
            static evmc::Result execute(const evmc_message &m) noexcept
            {
                const int64_t gas = 100;
                if (m.gas < gas) {
                    return evmc::Result{
                        evmc_result{.status_code = EVMC_OUT_OF_GAS}};
                }
                return evmc::Result{evmc_result{
                    .status_code = EVMC_SUCCESS,
                    .gas_left = m.gas - gas,
                    .output_size = 0u}};
            }
        };
    }
}

MONAD_EXECUTION_NAMESPACE_END
