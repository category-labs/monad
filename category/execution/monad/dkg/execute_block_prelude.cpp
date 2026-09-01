// Copyright (C) 2026 Category Labs, Inc.

#include <category/core/likely.h>
#include <category/core/assert.h>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/dkg/dkg_contract.hpp>
#include <category/execution/monad/dkg/execute_block_prelude.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_NAMESPACE_BEGIN

namespace dkg
{

    template <Traits traits>
    void execute_block_prelude(State &state)
    {
        if constexpr (traits::monad_rev() < MONAD_NEXT) {
            return;
        }

        // A Solidity deployment used to create the account that owns DKG
        // storage. The native contract has no deployment transaction, so
        // execution must create its trie account deterministically when the
        // native contract activates. A non-zero nonce keeps the otherwise
        // code-less system account from being pruned as an empty account.
        if (MONAD_UNLIKELY(!state.account_exists(DKG_CA))) {
            state.set_nonce(DKG_CA, 1);
        }
        if (state.account_exists(staking::STAKING_CA)) {
            MONAD_ASSERT(initialize_states(state));
        }
    }

    EXPLICIT_MONAD_TRAITS(execute_block_prelude);

}

MONAD_NAMESPACE_END
