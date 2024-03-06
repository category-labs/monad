#include <monad/evm/call_parameters.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/system_state.hpp>
#include <monad/state3/state.hpp>

MONAD_EVM_NAMESPACE_BEGIN

ExecutionState::ExecutionState(
    State &state, BlockHeader const &header, byte_string_view const code,
    Address const &sender, Address const &origin, Address const &recipient,
    uint64_t const gas, uint256_t const &value, uint256_t const &gas_price,
    byte_string_view const input_data, size_t const depth,
    bool const can_modify_state)
    : env{ExecutionEnvironment{
          .address = recipient,
          .origin = origin,
          .gas_price = gas_price,
          .input_data = input_data,
          .sender = sender,
          .value = value,
          .code = byte_string{code},
          .header = header,
          .depth = depth,
          .can_modify_state = can_modify_state}}
    , mstate{MachineState{.gas_left = gas, .pc = 0, .memory = {}, .stack = {}}}
    , sstate{recipient, state}
    , last_return_data{}
    , gas_refund{0}
    , analysis{analyze(code)}
{
}

ExecutionState::ExecutionState(
    State &state, BlockHeader const &header, CallParameters const &params)
    : ExecutionState(
          state, header, state.get_code(params.code_address)->executable_code,
          params.sender, params.origin, params.recipient, params.gas,
          params.value, params.gas_price, params.input_data, params.depth,
          params.can_modify_state)
{
}

MONAD_EVM_NAMESPACE_END
