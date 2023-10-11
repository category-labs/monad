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
}

MONAD_EXECUTION_NAMESPACE_END
