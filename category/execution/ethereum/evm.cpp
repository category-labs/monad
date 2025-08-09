#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/explicit_evmc_revision.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <ethash/hash_types.hpp>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmone/baseline.hpp>
#include <intx/intx.hpp>

#include <algorithm>
#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bool sender_has_balance(
    EvmcHostBase const &host, evmc_message const &msg) noexcept
{
    auto const value = intx::be::load<uint256_t>(msg.value);
    auto const balance =
        intx::be::load<uint256_t>(host.get_balance(msg.sender));
    return balance >= value;
}

void transfer_balances(
    State &state, evmc_message const &msg, Address const &to) noexcept
{
    auto const value = intx::be::load<uint256_t>(msg.value);
    state.subtract_from_balance(msg.sender, value);
    state.add_to_balance(to, value);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
Create<rev>::Create(
    Chain const &chain, State &state, BlockHeader const &header,
    CallTracerBase &call_tracer)
    : chain_(chain)
    , state_(state)
    , header_(header)
    , call_tracer_(call_tracer)
{
}

template <evmc_revision rev>
evmc::Result Create<rev>::deploy_contract_code(
    Address const &address, evmc::Result result) noexcept
{
    MONAD_ASSERT(result.status_code == EVMC_SUCCESS);

    // EIP-3541
    if constexpr (rev >= EVMC_LONDON) {
        if (result.output_size > 0 && result.output_data[0] == 0xef) {
            return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
        }
    }
    // EIP-170
    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        if (result.output_size >
            chain_.get_max_code_size(header_.number, header_.timestamp)) {
            return evmc::Result{EVMC_OUT_OF_GAS};
        }
    }

    auto const deploy_cost = static_cast<int64_t>(result.output_size) * 200;

    if (result.gas_left < deploy_cost) {
        if constexpr (rev == EVMC_FRONTIER) {
            // From YP: "No code is deposited in the state if the gas
            // does not cover the additional per-byte contract deposit
            // fee, however, the value is still transferred and the
            // execution side- effects take place."
            result.create_address = address;
            state_.set_code(address, {});
        }
        else {
            // EIP-2: If contract creation does not have enough gas to
            // pay for the final gas fee for adding the contract code to
            // the state, the contract creation fails (ie. goes
            // out-of-gas) rather than leaving an empty contract.
            result.status_code = EVMC_OUT_OF_GAS;
        }
    }
    else {
        result.create_address = address;
        result.gas_left -= deploy_cost;
        state_.set_code(address, {result.output_data, result.output_size});
    }
    return result;
}

template <evmc_revision rev>
evmc::Result
Create<rev>::operator()(EvmcHostBase &host, evmc_message const &msg) noexcept
{
    MONAD_ASSERT(msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2);

    call_tracer_.on_enter(msg);

    if (MONAD_UNLIKELY(!sender_has_balance(host, msg))) {
        evmc::Result result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        call_tracer_.on_exit(result);
        return result;
    }

    auto const nonce = state_.get_nonce(msg.sender);
    if (nonce == std::numeric_limits<decltype(nonce)>::max()) {
        // overflow
        evmc::Result result{EVMC_ARGUMENT_OUT_OF_RANGE, msg.gas};
        call_tracer_.on_exit(result);
        return result;
    }
    state_.set_nonce(msg.sender, nonce + 1);

    Address const contract_address = [&] {
        if (msg.kind == EVMC_CREATE) {
            return create_contract_address(msg.sender, nonce); // YP Eqn. 85
        }
        else { // msg.kind == EVMC_CREATE2
            auto const code_hash = keccak256({msg.input_data, msg.input_size});
            return create2_contract_address(
                msg.sender, msg.create2_salt, code_hash);
        }
    }();

    state_.access_account(contract_address);

    // Prevent overwriting contracts - EIP-684
    if (state_.get_nonce(contract_address) != 0 ||
        state_.get_code_hash(contract_address) != NULL_HASH) {
        evmc::Result result{EVMC_INVALID_INSTRUCTION};
        call_tracer_.on_exit(result);
        return result;
    }

    state_.push();

    state_.create_contract(contract_address);

    // EIP-161
    constexpr auto starting_nonce = rev >= EVMC_SPURIOUS_DRAGON ? 1 : 0;
    state_.set_nonce(contract_address, starting_nonce);
    transfer_balances(state_, msg, contract_address);

    evmc_message const m_call{
        .kind = EVMC_CALL,
        .flags = 0,
        .depth = msg.depth,
        .gas = msg.gas,
        .recipient = contract_address,
        .sender = msg.sender,
        .input_data = nullptr,
        .input_size = 0,
        .value = msg.value,
        .create2_salt = {},
        .code_address = contract_address,
        .code = nullptr,
        .code_size = 0,
    };

    auto result = state_.vm().execute_raw(
        rev,
        &host.get_interface(),
        host.to_context(),
        &m_call,
        {msg.input_data, msg.input_size});

    if (result.status_code == EVMC_SUCCESS) {
        result = deploy_contract_code(contract_address, std::move(result));
    }

    if (result.status_code == EVMC_SUCCESS) {
        state_.pop_accept();
    }
    else {
        result.gas_refund = 0;
        if (result.status_code != EVMC_REVERT) {
            result.gas_left = 0;
        }
        bool const ripemd_touched = state_.is_touched(ripemd_address);
        state_.pop_reject();
        if (MONAD_UNLIKELY(ripemd_touched)) {
            // YP K.1. Deletion of an Account Despite Out-of-gas.
            state_.touch(ripemd_address);
        }
    }

    call_tracer_.on_exit(result);

    return result;
}

template class Create<EVMC_FRONTIER>;
template class Create<EVMC_HOMESTEAD>;
template class Create<EVMC_TANGERINE_WHISTLE>;
template class Create<EVMC_SPURIOUS_DRAGON>;
template class Create<EVMC_BYZANTIUM>;
template class Create<EVMC_CONSTANTINOPLE>;
template class Create<EVMC_PETERSBURG>;
template class Create<EVMC_ISTANBUL>;
template class Create<EVMC_BERLIN>;
template class Create<EVMC_LONDON>;
template class Create<EVMC_PARIS>;
template class Create<EVMC_SHANGHAI>;
template class Create<EVMC_CANCUN>;
template class Create<EVMC_PRAGUE>;

template <evmc_revision rev>
Call<rev>::Call(
    State &state, CallTracerBase &call_tracer, Chain const &chain, uint64_t i,
    void *chain_context)
    : state_(state)
    , call_tracer_(call_tracer)
    , chain_(chain)
    , i_(i)
    , chain_context_(chain_context)
{
}

template <evmc_revision rev>
std::optional<evmc::Result>
Call<rev>::pre_call(EvmcHostBase const &host, evmc_message const &msg)
{
    state_.push();

    if (msg.kind != EVMC_DELEGATECALL) {
        if (MONAD_UNLIKELY(!sender_has_balance(host, msg))) {
            state_.pop_reject();
            return evmc::Result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        }
        else if (msg.flags != EVMC_STATIC) {
            transfer_balances(state_, msg, msg.recipient);
        }
    }

    MONAD_ASSERT(
        msg.kind != EVMC_CALL ||
        Address{msg.recipient} == Address{msg.code_address});
    if (msg.kind == EVMC_CALL && msg.flags & EVMC_STATIC) {
        // eip-161
        state_.touch(msg.recipient);
    }

    return std::nullopt;
}

template <evmc_revision rev>
void Call<rev>::post_call(evmc::Result const &result)
{
    MONAD_ASSERT(result.status_code == EVMC_SUCCESS || result.gas_refund == 0);
    MONAD_ASSERT(
        result.status_code == EVMC_SUCCESS ||
        result.status_code == EVMC_REVERT || result.gas_left == 0);

    if (result.status_code == EVMC_SUCCESS) {
        state_.pop_accept();
    }
    else {
        bool const ripemd_touched = state_.is_touched(ripemd_address);
        state_.pop_reject();
        if (MONAD_UNLIKELY(ripemd_touched)) {
            // YP K.1. Deletion of an Account Despite Out-of-gas.
            state_.touch(ripemd_address);
        }
    }
}

template <evmc_revision rev>
evmc::Result
Call<rev>::operator()(EvmcHostBase &host, evmc_message const &msg) noexcept
{
    MONAD_ASSERT(
        msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE ||
        msg.kind == EVMC_CALL);

    call_tracer_.on_enter(msg);

    if (auto result = pre_call(host, msg); result.has_value()) {
        call_tracer_.on_exit(result.value());
        return std::move(result.value());
    }

    evmc::Result result;
    if (auto maybe_result = check_call_precompile<rev>(msg);
        maybe_result.has_value()) {
        result = std::move(maybe_result.value());
    }
    else {
        auto const hash = state_.get_code_hash(msg.code_address);
        auto const &code = state_.read_code(hash);
        result = state_.vm().execute(
            rev, &host.get_interface(), host.to_context(), &msg, hash, code);
    }

    evmc_tx_context const tx_context = host.get_tx_context();
    if (msg.depth == 0 && chain_.revert_transaction(
                              static_cast<uint64_t>(tx_context.block_number),
                              static_cast<uint64_t>(tx_context.block_timestamp),
                              i_,
                              msg.sender,
                              state_,
                              chain_context_)) {
        result.status_code = EVMC_REVERT;
        result.gas_refund = 0;
    }
    post_call(result);
    call_tracer_.on_exit(result);
    return result;
}

template class Call<EVMC_FRONTIER>;
template class Call<EVMC_HOMESTEAD>;
template class Call<EVMC_TANGERINE_WHISTLE>;
template class Call<EVMC_SPURIOUS_DRAGON>;
template class Call<EVMC_BYZANTIUM>;
template class Call<EVMC_CONSTANTINOPLE>;
template class Call<EVMC_PETERSBURG>;
template class Call<EVMC_ISTANBUL>;
template class Call<EVMC_BERLIN>;
template class Call<EVMC_LONDON>;
template class Call<EVMC_PARIS>;
template class Call<EVMC_SHANGHAI>;
template class Call<EVMC_CANCUN>;
template class Call<EVMC_PRAGUE>;

MONAD_NAMESPACE_END
