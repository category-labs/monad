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

#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/contract/storage_array.hpp>
#include <category/execution/ethereum/core/contract/storage_variable.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_contract.hpp>
#include <category/execution/monad/reserve_balance/reserve_balance_error.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

//
// ABI
//

static constexpr uint32_t UPDATE_SELECTOR =
    abi_encode_selector("update(uint256)");
static_assert(UPDATE_SELECTOR == 0x82ab890a);

//
// Gas Costs
//

// The gas for the reserve balance precompile are determined by sload, sstores
// and events. The gas cost is calculated as:
//
// gas = COLD_SLOAD_COST * number_of_cold_sloads +
//       WARM_NONZERO_SSTORE_COST * number_of_warm_nonzero_sstores +
//       EVENT_COST * number_of_events
//

constexpr uint64_t COLD_SLOAD_COST = 8100;
constexpr uint64_t WARM_SSTORE_NONZERO_COST = 2900;
constexpr uint64_t EVENT_COSTS = 4275;
constexpr uint64_t UPDATE_OP_COST =
    COLD_SLOAD_COST + WARM_SSTORE_NONZERO_COST + EVENT_COSTS;
constexpr uint64_t FALLBACK_COST = 40'000;

static_assert(UPDATE_OP_COST == 15275);

Result<void> function_not_payable(u256_be const &value)
{
    if (MONAD_UNLIKELY(!value.is_zero())) {
        return ReserveBalanceError::ValueNonZero;
    }

    return outcome::success();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bool is_reconfiguring_transaction(Transaction const &tx)
{
    if (tx.to == RESERVE_BALANCE_CA && tx.value == 0 &&
        tx.data.size() >= sizeof(uint32_t)) {
        unsigned char const *b =
            reinterpret_cast<uint8_t const *>(tx.data.data());
        uint32_t const selector = (uint32_t(b[0]) << 24) |
                                  (uint32_t(b[1]) << 16) |
                                  (uint32_t(b[2]) << 8) | (uint32_t(b[3]));
        return selector == UPDATE_SELECTOR;
    }
    return false;
}

struct ReserveBalanceState
{

    static constexpr uint64_t PENDING_MASK = 0x01;
    static constexpr uint64_t INITIALIZED_MASK = 0x02;

    std::optional<uint256_t> pending_value;
    uint256_t settled_value;
    uint64_t pending_block;
    uint64_t settled_block;

    ReserveBalanceState()
        : pending_value(std::nullopt)
        , settled_value(DEFAULT_RESERVE_BALANCE_WEI)
        , pending_block(0)
        , settled_block(0)
    {
    }

    ReserveBalanceState(
        std::optional<uint256_t> pending_value, uint256_t settled_value,
        uint64_t pending_block, uint64_t settled_block)
        : pending_value(pending_value)
        , settled_value(settled_value)
        , pending_block(pending_block)
        , settled_block(settled_block)
    {
    }

    static ReserveBalanceState load(State &state, Address const &offset)
    {
        bytes32_t key{};
        std::memcpy(key.bytes, offset.bytes, sizeof(Address));
        MONAD_ASSERT(key.bytes[20] == 0x00);
        bytes32_t const &packed = state.get_storage(RESERVE_BALANCE_CA, key);

        // Check whether we are loading an uninitialized reserve balance state
        // (i.e. the first load for an address).
        if (MONAD_UNLIKELY(packed == bytes32_t{})) {
            return ReserveBalanceState();
        }

        uint64_t flags = 0;
        std::memcpy(&flags, packed.bytes, sizeof(uint64_t));
        uint64_t pending_block = 0;
        std::memcpy(
            &pending_block, packed.bytes + sizeof(uint64_t), sizeof(uint64_t));
        uint64_t settled_block = 0;
        std::memcpy(
            &settled_block,
            packed.bytes + 2 * sizeof(uint64_t),
            sizeof(uint64_t));

        key.bytes[20] = 0x01;
        bytes32_t const &settled_value_raw =
            state.get_storage(RESERVE_BALANCE_CA, key);
        uint256_t const settled_value =
            intx::le::load<uint256_t>(settled_value_raw.bytes);

        std::optional<uint256_t> const pending_value =
            [&]() -> std::optional<uint256_t> {
            if ((flags & PENDING_MASK) == 0) {
                return std::nullopt;
            }
            key.bytes[20] = 0x02;
            bytes32_t const &pending_value_raw =
                state.get_storage(RESERVE_BALANCE_CA, key);
            return intx::le::load<uint256_t>(pending_value_raw.bytes);
        }();

        return ReserveBalanceState(
            pending_value, settled_value, pending_block, settled_block);
    }

    void store(State &state, Address const &address)
    {
        bytes32_t key{};
        std::memcpy(key.bytes, address.bytes, sizeof(Address));
        MONAD_ASSERT(key.bytes[20] == 0x00);

        {
            uint64_t const flags =
                INITIALIZED_MASK |
                (pending_value.has_value() ? PENDING_MASK : 0x00);
            uint256_t const packed{
                flags,
                pending_block,
                settled_block,
                0x00,
            };

            bytes32_t encoded{};
            intx::le::store(encoded.bytes, packed);
            state.set_storage(RESERVE_BALANCE_CA, key, encoded);
        }

        {
            key.bytes[20] = 0x01;
            bytes32_t encoded{};
            intx::le::store(encoded.bytes, settled_value);
            state.set_storage(RESERVE_BALANCE_CA, key, encoded);
        }

        {
            key.bytes[20] = 0x02;
            bytes32_t encoded{};
            if (pending_value.has_value()) {
                intx::le::store(encoded.bytes, *pending_value);
            }
            state.set_storage(RESERVE_BALANCE_CA, key, encoded);
        }

        // StorageArray<uint256_t> data{state, RESERVE_BALANCE_CA, key};
        // MONAD_ASSERT(data.length() == 3);
        // uint256_t const packed{
        //     pending_value.has_value() ? 1 : 0,
        //     pending_block,
        //     settled_block,
        // };
        // data.get(0).store(packed);
        // data.get(1).store(settled_value);
        // if (pending_value.has_value()) {
        //     data.get(2).store(pending_value.value());
        // }
        // else {
        //     data.get(2).clear();
        // }
    }
};

ReserveBalanceContract::ReserveBalanceContract(
    State &state, CallTracerBase &tracer)
    : state_{state}
    , call_tracer_{tracer}
{
    state_.add_to_balance(RESERVE_BALANCE_CA, 0);
}

Result<uint256_t> ReserveBalanceContract::update(
    State &state, Address const &sender, uint256_t const &new_value)
{
    ReserveBalanceState rb_state = ReserveBalanceState::load(state, sender);

    uint256_t const old_settled_value = rb_state.settled_value;
    uint64_t const block_number = state.incarnation().get_block();
    // Lazy promotion: promote pending to settled if delay has passed
    if (rb_state.pending_value.has_value() &&
        rb_state.pending_block + DELAY_BLOCKS <= block_number) {
        rb_state.settled_value = *rb_state.pending_value;
        rb_state.pending_value = std::nullopt;
        rb_state.settled_block = rb_state.pending_block;
        rb_state.pending_block = 0;
    }

    // Reject if there is a pending update.
    if (rb_state.pending_value.has_value()) {
        return ReserveBalanceError::PendingUpdate;
    }
    rb_state.pending_value = new_value;
    rb_state.pending_block = block_number;
    rb_state.store(state, sender);
    return old_settled_value;
}

void ReserveBalanceContract::emit_reserve_balance_changed_event(
    bytes32_t const &sender, u256_be const &old_value, u256_be const &new_value)
{
    static constexpr auto signature = abi_encode_event_signature(
        "ReserveBalanceChanged(address,uint256,uint256)");
    static_assert(
        signature ==
        0xecbead9d902aef6900edfcf4e3ec205b52f4f59866d086bbf0d6388fc9b30d97_bytes32);

    auto const event = EventBuilder(RESERVE_BALANCE_CA, signature)
                           .add_topic(sender)
                           .add_data(abi_encode_uint(old_value))
                           .add_data(abi_encode_uint(new_value))
                           .build();
    state_.store_log(event);
    call_tracer_.on_log(event);
}

template <Traits traits>
std::pair<ReserveBalanceContract::PrecompileFunc, uint64_t>
ReserveBalanceContract::precompile_dispatch(byte_string_view &input)
{
    if (MONAD_UNLIKELY(input.size() < 4)) {
        return {&ReserveBalanceContract::precompile_fallback, FALLBACK_COST};
    }

    auto const signature =
        intx::be::unsafe::load<uint32_t>(input.substr(0, 4).data());
    input.remove_prefix(4);

    switch (signature) {
    case UPDATE_SELECTOR:
        return {&ReserveBalanceContract::precompile_update, UPDATE_OP_COST};
    default:
        return {&ReserveBalanceContract::precompile_fallback, FALLBACK_COST};
    }
}

EXPLICIT_MONAD_TRAITS(ReserveBalanceContract::precompile_dispatch);

Result<byte_string> ReserveBalanceContract::precompile_update(
    byte_string_view input, evmc_address const &sender,
    evmc_bytes32 const &msg_value)
{
    BOOST_OUTCOME_TRY(function_not_payable(u256_be::from_bytes(msg_value)));
    BOOST_OUTCOME_TRY(auto new_value_be, abi_decode_fixed<u256_be>(input));

    if (MONAD_UNLIKELY(!input.empty())) {
        return ReserveBalanceError::InvalidInput;
    }

    if (new_value_be.is_zero()) {
        new_value_be = u256_be{DEFAULT_RESERVE_BALANCE_WEI};
    }

    bytes32_t const encoded_address = abi_encode_address(sender);

    BOOST_OUTCOME_TRY(
        auto const old_value, update(state_, sender, new_value_be.native()));
    u256_be const old_value_be{old_value};

    emit_reserve_balance_changed_event(
        encoded_address, old_value_be, new_value_be);

    return byte_string{abi_encode_bool(true)};
}

Result<byte_string> ReserveBalanceContract::precompile_fallback(
    byte_string_view, evmc_address const &, evmc_uint256be const &)
{
    return ReserveBalanceError::MethodNotSupported;
}

ReserveBalanceView::ReserveBalanceView(State &state)
    : state_(state)
{
    state_.add_to_balance(RESERVE_BALANCE_CA, 0);
}

uint256_t ReserveBalanceView::get_delayed_urb(Address const &address)
{
    ReserveBalanceState rb_state = ReserveBalanceState::load(state_, address);

    // If a pending update was made by block N - DELAY_BLOCKS, then use it.
    if (rb_state.pending_value.has_value() &&
        rb_state.pending_block <=
            state_.incarnation().get_block() - DELAY_BLOCKS) {
        return *rb_state.pending_value;
    }

    return rb_state.settled_value;
}

MONAD_NAMESPACE_END
