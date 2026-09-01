// Copyright (C) 2026 Category Labs, Inc.

#pragma once

#include <category/core/config.hpp>
#include <category/vm/evm/traits.hpp>

MONAD_NAMESPACE_BEGIN

class State;

namespace dkg
{

    template <Traits traits>
    void execute_block_prelude(State &);

}

MONAD_NAMESPACE_END
