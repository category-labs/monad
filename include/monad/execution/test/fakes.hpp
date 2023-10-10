#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>

#include <monad/execution/config.hpp>

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
        bytes32_t state_root() const noexcept { return {}; }
    };

    template <class TState, class TTraits>
    struct EvmHost
    {
        static inline evmc_result _result{.status_code = EVMC_SUCCESS};
        static inline Receipt _receipt{};

        EvmHost() = default;

        EvmHost(EvmHost const &, TState &) {}

        EvmHost(BlockHeader const &, Transaction const &, TState &) noexcept {}

        [[nodiscard]] static inline constexpr evmc_message
        make_msg_from_txn(Transaction const &)
        {
            return {.kind = EVMC_CALL};
        };

        [[nodiscard]] inline constexpr Receipt make_receipt_from_result(
            evmc_status_code, Transaction const &t,
            uint64_t const gas_remaining)
        {
            _receipt.gas_used = t.gas_limit - gas_remaining;
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

    namespace traits
    {
        template <class TState>
        struct alpha
        {
            using next_fork_t = alpha;

            static constexpr evmc_revision rev = EVMC_FRONTIER;
            static inline uint64_t last_block_number{
                std::numeric_limits<uint64_t>::max()};
            static constexpr uint64_t n_precompiles = 4;
            static inline uint64_t _intrinsic_gas{21'000u};
            static inline uint64_t _max_refund_quotient{2u};
            static inline uint64_t _create_address{};
            static constexpr void apply_block_award(TState &, Block const &) {}
            static constexpr uint256_t calculate_txn_award(
                Transaction const &, uint256_t const &gas_cost,
                uint64_t gas_used)
            {
                return gas_cost * uint256_t{gas_used};
            }
            static auto intrinsic_gas(Transaction const &)
            {
                return _intrinsic_gas;
            }
            static auto starting_nonce() { return 1u; }
            static auto max_refund_quotient() { return _max_refund_quotient; }
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

            static constexpr uint256_t
            gas_price(Transaction const &, uint256_t const &c)
            {
                return c;
            }

            static constexpr void
            transfer_balance_dao(TState &, block_num_t const)
            {
            }

            static constexpr void validate_block(Block const &) {}

            static constexpr void warm_coinbase(TState &, address_t const &) {}

            static constexpr void process_withdrawal(
                TState &,
                std::optional<std::vector<Withdrawal>> const &) noexcept
            {
            }

            [[nodiscard]] static constexpr bool
            transaction_type_valid(TransactionType const)
            {
                return true;
            }

            [[nodiscard]] static constexpr bool
            account_exists(TState &state, address_t const &address)
            {
                return state.account_exists(address);
            }

            static constexpr void
            populate_chain_id(evmc_tx_context &context) noexcept
            {
                intx::be::store(context.chain_id.bytes, intx::uint256{1});
            }

            [[nodiscard]] static constexpr bool
            init_code_valid(Transaction const &) noexcept
            {
                return true;
            }
        };

        template <class TState>
        struct beta : public alpha<TState>
        {
            using next_fork_t = beta;

            static constexpr evmc_revision rev = EVMC_HOMESTEAD;
            static inline uint64_t last_block_number{
                std::numeric_limits<uint64_t>::max()};
        };
    }
}

MONAD_EXECUTION_NAMESPACE_END
