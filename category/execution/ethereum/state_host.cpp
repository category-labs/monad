// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/throw.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/evm/tx_context.hpp>
#if defined(MONAD_ZKVM_ZISK)
    #include <category/vm/evm/delegation.hpp>
    #include <category/vm/evm/explicit_traits.hpp>
#endif

#include <cstddef>
#include <cstdint>
#include <type_traits>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

StateHostBase::StateHostBase(
    CallTracerBase &call_tracer, trace::StateTracer &state_tracer,
    vm::TxContext const &tx_context, BlockHashBuffer const &block_hash_buffer,
    State &state, bool const log_native_transfers) noexcept
    : block_hash_buffer_{block_hash_buffer}
    , tx_context_{tx_context}
    , state_{state}
    , call_tracer_{call_tracer}
    , log_native_transfers_{log_native_transfers}
    , state_tracer_{state_tracer}
{
}

bytes32_t
StateHostBase::get_storage(Address const &address, bytes32_t const &key) const
{
    MONAD_TRY
    {
        return state_.get_storage(address, key);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

StorageStatus StateHostBase::set_storage(
    Address const &address, bytes32_t const &key,
    bytes32_t const &value) noexcept
{
    MONAD_TRY
    {
        return state_.set_storage(address, key, value);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

uint256_t StateHostBase::get_balance(Address const &address) const
{
    MONAD_TRY
    {
        return state_.get_balance(address);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

size_t StateHostBase::get_code_size(Address const &address) const
{
    MONAD_TRY
    {
        if (MONAD_UNLIKELY(trace::is_code_tracer(state_tracer_))) {
            bytes32_t const hash = state_.get_code_hash(address);
            if (hash == NULL_HASH) {
                return 0;
            }
            auto const vcode = state_.read_code(hash);
            MONAD_ASSERT(vcode);
            trace::on_read_code(state_tracer_, hash, vcode->intercode());
            return vcode->intercode()->size();
        }
        return state_.get_code_size(address);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

bytes32_t StateHostBase::get_code_hash(Address const &address) const
{
    MONAD_TRY
    {
        if (state_.account_is_dead(address)) {
            return bytes32_t{};
        }
        return state_.get_code_hash(address);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

namespace
{
    // Load code and notify the tracer, or return empty for NULL_HASH.
    vm::SharedVarcode read_code_for_tracer(
        State &state, trace::StateTracer &tracer, monad_address const &address)
    {
        bytes32_t const hash = state.get_code_hash(address);
        if (hash == NULL_HASH) {
            return {};
        }
        auto vcode = state.read_code(hash);
        MONAD_ASSERT(vcode);
        trace::on_read_code(tracer, hash, vcode->intercode());
        return vcode;
    }
}

size_t StateHostBase::copy_code(
    Address const &address, size_t const offset, uint8_t *const data,
    size_t const size) const
{
    MONAD_TRY
    {
        if (MONAD_UNLIKELY(trace::is_code_tracer(state_tracer_))) {
            auto const vcode =
                read_code_for_tracer(state_, state_tracer_, address);
            if (!vcode) {
                return 0;
            }
            return vcode->intercode()->copy_code(offset, data, size);
        }
        return state_.copy_code(address, offset, data, size);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

#if defined(MONAD_ZKVM_ZISK)
std::optional<Address>
StateHostBase::delegate_of(monad_address const &address) const noexcept
{
    MONAD_TRY
    {
        if (MONAD_UNLIKELY(trace::is_code_tracer(state_tracer_))) {
            auto const vcode =
                read_code_for_tracer(state_, state_tracer_, address);
            if (!vcode) {
                return std::nullopt;
            }
            return vm::evm::designation_of(vcode->intercode()->code_span());
        }
        return state_.delegate_of(address);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}
#endif

vm::TxContext const *StateHostBase::get_tx_context() const noexcept
{
    return &tx_context_;
}

// This attempts to read from the contract first before falling back to the
// block hash buffer. This is currently only called by the BLOCKHASH
// implementation which guarantees that the block_number is in range.
bytes32_t StateHostBase::get_block_hash(int64_t const block_number) const
{
    MONAD_TRY
    {
        MONAD_ASSERT(block_number >= 0);
        if (bytes32_t const block_hash = get_block_hash_history(
                state_, static_cast<uint64_t>(block_number));
            block_hash != bytes32_t{}) {
            return block_hash;
        }
        bytes32_t const block_hash =
            block_hash_buffer_.get(static_cast<uint64_t>(block_number));
        MONAD_ASSERT(block_hash != bytes32_t{});
        return block_hash;
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

void StateHostBase::emit_log(
    Address const &address, uint8_t const *const data, size_t const data_size,
    bytes32_t const topics[], size_t const num_topics)
{
    MONAD_TRY
    {
        static_assert(std::is_convertible_v<bytes32_t const &, bytes32_t>);
#if defined(MONAD_ZKVM_ZISK)
        // Construct the Log in place without moving temporary data or topics.
        struct LogBuilder
        {
            Address const &address;
            uint8_t const *data;
            size_t data_size;
            bytes32_t const *topics;
            size_t num_topics;

            operator Receipt::Log() const
            {
                return Receipt::Log{
                    .data = {data, data_size},
                    // LOG0 may supply nullptr: do not form a range from it.
                    .topics = num_topics == 0
                                  ? std::vector<bytes32_t>{}
                                  : std::vector<
                                        bytes32_t>{topics, topics + num_topics},
                    .address = address};
            }
        };

        Receipt::Log const &log = state_.emplace_log(
            LogBuilder{address, data, data_size, topics, num_topics});
        call_tracer_.on_log(log);
        return;
#else
        Receipt::Log log{.data = {data, data_size}, .address = address};
        // Copy all topics in one range.
        if (num_topics != 0) {
            log.topics.assign(topics, topics + num_topics);
        }
        // Trace before moving the log into state.
        call_tracer_.on_log(log);
        state_.store_log(std::move(log));
        return;
#endif
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

bytes32_t StateHostBase::get_transient_storage(
    Address const &address, bytes32_t const &key) const
{
    MONAD_TRY
    {
        return state_.get_transient_storage(address, key);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

void StateHostBase::set_transient_storage(
    Address const &address, bytes32_t const &key, bytes32_t const &value)
{
    MONAD_TRY
    {
        return state_.set_transient_storage(address, key, value);
    }
    MONAD_CATCH(...)
    {
        capture_current_exception();
    }
    stack_unwind();
}

MONAD_NAMESPACE_END
#if defined(MONAD_ZKVM_ZISK)

namespace monad::vm::runtime
{
    template <Traits traits>
    [[gnu::noinline]] AccessStatus guest_sload_into(
        Host &host, Address const &address, bytes32_t const &key,
        bool const can_pay_cold_access, uint256_t &value) noexcept
    {
        return static_cast<StateHost<traits> &>(host).sload_into(
            address, key, can_pay_cold_access, value);
    }

    EXPLICIT_TRAITS(guest_sload_into);

    template <Traits traits>
    SstoreStatus guest_sstore_into(
        Host &host, Address const &address, bytes32_t const &key,
        bytes32_t const &value, bool const can_pay_cold_access) noexcept
    {
        return static_cast<StateHost<traits> &>(host).sstore_into(
            address, key, value, can_pay_cold_access);
    }

    EXPLICIT_TRAITS(guest_sstore_into);

    template <Traits traits>
    AccessStatus
    guest_access_account(Host &host, Address const &address) noexcept
    {
        return static_cast<StateHost<traits> &>(host).access_account(address);
    }

    EXPLICIT_TRAITS(guest_access_account);

    template <Traits traits>
    vm::Result guest_call(Host &host, Message const &message) noexcept
    {
        return static_cast<StateHost<traits> &>(host).call(message);
    }

    EXPLICIT_TRAITS(guest_call);

    bytes32_t guest_get_transient_storage(
        Host const &host, Address const &address, bytes32_t const &key) noexcept
    {
        return static_cast<StateHostBase const &>(host)
            .StateHostBase::get_transient_storage(address, key);
    }

    void guest_set_transient_storage(
        Host &host, Address const &address, bytes32_t const &key,
        bytes32_t const &value) noexcept
    {
        static_cast<StateHostBase &>(host).StateHostBase::set_transient_storage(
            address, key, value);
    }

    TxContext const *guest_get_tx_context(Host const &host) noexcept
    {
        return static_cast<StateHostBase const &>(host)
            .StateHostBase::get_tx_context();
    }

    size_t
    guest_get_code_size(Host const &host, Address const &address) noexcept
    {
        return static_cast<StateHostBase const &>(host)
            .StateHostBase::get_code_size(address);
    }

    uint256_t
    guest_get_balance(Host const &host, Address const &address) noexcept
    {
        return static_cast<StateHostBase const &>(host)
            .StateHostBase::get_balance(address);
    }

    void guest_emit_log(
        Host &host, Address const &address, uint8_t const *const data,
        size_t const data_size, bytes32_t const topics[],
        size_t const num_topics) noexcept
    {
        static_cast<StateHostBase &>(host).StateHostBase::emit_log(
            address, data, data_size, topics, num_topics);
    }

    std::optional<Address>
    guest_delegate_of(Host const &host, monad_address const &address) noexcept
    {
        return static_cast<StateHostBase const &>(host)
            .StateHostBase::delegate_of(address);
    }
}
#endif
