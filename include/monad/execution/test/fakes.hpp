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
#include <monad/core/withdrawal.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/static_precompiles.hpp>

#include <monad/state/state_changes.hpp>

#include <evmc/evmc.hpp>

#include <tl/expected.hpp>

#include <ethash/keccak.hpp>

#include <bit>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

namespace fake
{
    struct InnerStorage
    {
        std::string storage_;
    };

    class BlockDb
    {
    public:
        enum class Status
        {
            SUCCESS,
            NO_BLOCK_FOUND,
            DECOMPRESS_ERROR,
            DECODE_ERROR
        };

        block_num_t _last_block_number{};

        Status get(block_num_t const block_number, Block &) const
        {
            if (block_number <= _last_block_number) {
                return Status::SUCCESS;
            }
            else {
                return Status::NO_BLOCK_FOUND;
            }
        }

        [[nodiscard]] bytes32_t get_block_hash(block_num_t) { return {}; }
    };

    struct Db
    {
        void create(address_t const &, Account const &) const noexcept
        {
            return;
        }
        void commit(state::StateChanges const &) const noexcept { return; }
        bytes32_t state_root() const noexcept { return {}; }
    };

    struct AccountState
    {
        Db db_;
    };

    struct State
    {
        struct ChangeSet
        {
            struct AccountChangeSet
            {
                std::string changed_{};
            };

            struct StorageChangeSet
            {
                InnerStorage touched_;
            };

            struct CodeChangeSet
            {
                std::string code_{};
            };

            AccountChangeSet accounts_;
            StorageChangeSet storage_;
            CodeChangeSet code_;

            std::unordered_map<address_t, Account> _accounts{};
            std::unordered_map<bytes32_t, byte_string> _code{};

            std::vector<Receipt::Log> _logs{};
            unsigned int _txn_id{};
            uint64_t _selfdestructs{};
            uint64_t _touched_dead{};
            uint64_t _suicides{};
            uint256_t _reward{};

            ChangeSet() = default;

            ChangeSet(unsigned int id)
                : _txn_id{id}
            {
            }

            unsigned int txn_id() const noexcept { return _txn_id; }

            void create_account(address_t const &a) noexcept
            {
                _accounts.insert({a, Account{}});
            }

            // EVMC Host Interface
            [[nodiscard]] bool account_exists(address_t const &a)
            {
                return _accounts.contains(a);
            }

            // EVMC Host Interface
            evmc_access_status access_account(address_t const &a) noexcept
            {
                if (!_accounts.contains(a)) {
                    _accounts.emplace(a, Account{});
                }
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

            void set_code(address_t const &a, byte_string const &c)
            {
                auto const code_hash = std::bit_cast<monad::bytes32_t const>(
                    ethash::keccak256(c.data(), c.size()));

                _code.insert({code_hash, c});
                if (!account_exists(a)) {
                    _accounts.emplace(a, Account{.code_hash = code_hash});
                }
                else {
                    _accounts.at(a).code_hash = code_hash;
                }
            }

            // EVMC Host Interface
            [[nodiscard]] size_t
            get_code_size(address_t const &a) const noexcept
            {
                return _code.at(get_code_hash(a)).size();
            }

            // EVMC Host Interface
            [[nodiscard]] size_t copy_code(
                address_t const &, size_t, uint8_t *, size_t) const noexcept
            {
                return 0u;
            }

            [[nodiscard]] byte_string_view
            get_code(bytes32_t const &b) const noexcept
            {
                if (b == NULL_HASH) {
                    return {};
                }
                return byte_string_view{_code.at(b)};
            }

            void revert() noexcept { _accounts.clear(); }

            [[nodiscard]] bytes32_t get_block_hash(int64_t) const noexcept
            {
                return {};
            }

            void store_log(Receipt::Log &&l) { _logs.emplace_back(l); }

            std::vector<Receipt::Log> &logs() { return _logs; }

            void add_txn_award(uint256_t const &amount) { _reward += amount; }
        };

        enum class MergeStatus
        {
            WILL_SUCCEED,
            TRY_LATER,
            COLLISION_DETECTED,
        };

        std::unordered_map<address_t, uint256_t> _block_reward{};

        void apply_block_reward(address_t const &a, uint256_t const &r)
        {
            _block_reward.insert({a, r});
        }

        void apply_ommer_reward(address_t const &a, uint256_t const &r)
        {
            _block_reward.insert({a, r});
        }

        // Had to name this variable using post_ because we access it directly
        AccountState accounts_{};

        unsigned int _current_txn{};

        MergeStatus _merge_status{MergeStatus::TRY_LATER};

        unsigned int current_txn() { return _current_txn; }

        ChangeSet get_new_changeset(unsigned int id) { return ChangeSet(id); }

        MergeStatus can_merge_changes(ChangeSet const &)
        {
            return _merge_status;
        }

        void merge_changes(ChangeSet &) { return; }

        void commit() const noexcept { return; }

        [[nodiscard]] bytes32_t get_state_hash() const { return {}; }

        constexpr void create_and_prune_block_history(uint64_t) const
        {
            return;
        }

        void warm_coinbase(address_t const &) { return; }
    };

    template <class TState, concepts::fork_traits<TState> TTraits, class TEvm>
    struct EvmHost
    {
        evmc_result _result{};
        Receipt _receipt{};

        EvmHost() = default;

        EvmHost(BlockHeader const &, Transaction const &, TState &) noexcept {}

        [[nodiscard]] static inline constexpr evmc_message
        make_msg_from_txn(Transaction const &)
        {
            return {.kind = EVMC_CALL};
        };

        [[nodiscard]] inline constexpr Receipt make_receipt_from_result(
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

        template <class TEvmHost>
        static evmc::Result
        execute(TEvmHost *, evmc_message const &, byte_string_view)
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
            static inline uint64_t _create_address{};
            static constexpr uint64_t _echo_gas_cost{10};
            static constexpr void apply_block_award(TState &, Block const &) {}
            static constexpr void apply_txn_award(
                TState &s, Transaction const &, uint64_t gas_cost,
                uint64_t gas_used)
            {
                s.add_txn_award(uint256_t{gas_cost} * uint256_t{gas_used});
            }
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

            static evmc::Result deploy_contract_code(
                TState &, address_t const &a, evmc::Result r) noexcept
            {
                if (r.status_code == EVMC_SUCCESS) {
                    r.create_address = a;
                }
                return r;
            }

            static constexpr uint64_t gas_price(Transaction const &, uint64_t c)
            {
                return c;
            }

            static constexpr void
            transfer_balance_dao(TState &, block_num_t const)
            {
            }

            static constexpr void warm_coinbase(TState &, address_t const &) {}

            static constexpr void process_withdrawal(
                TState &,
                std::optional<std::vector<Withdrawal>> const &) noexcept
            {
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
            static evmc::Result execute(evmc_message const &m) noexcept
            {
                int64_t const gas =
                    (int64_t const)(m.input_size * T::echo_gas_cost());
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
                    .release = [](evmc_result const *result) {
                        std::free((unsigned char *)result->output_data);
                    }}};
            }
        };

        struct OneHundredGas
        {
            static evmc::Result execute(evmc_message const &m) noexcept
            {
                int64_t const gas = 100;
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
