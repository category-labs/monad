#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>

MONAD_NAMESPACE_BEGIN

byte_string &read_code(bytes32_t const &, Code &, BlockState &);

MONAD_NAMESPACE_END
