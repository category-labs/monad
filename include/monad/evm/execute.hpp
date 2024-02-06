#pragma once

#include <monad/evm/config.hpp>
#include <monad/evm/revision.hpp>

#include <memory>

MONAD_EVM_NAMESPACE_BEGIN

struct ExecutionState;
enum class Status;

template <Revision rev>
Status execute(std::shared_ptr<ExecutionState>);

MONAD_EVM_NAMESPACE_END
