// Copyright (C) 2026 Category Labs, Inc.
//
// C++ layer test for TinyVM precompile: EIP-161 account creation.
// Backend behavior (registerToken, gas costs, proofs) is tested
// in the Rust monad-tinyvm crate.

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/tinyvm/tinyvm_precompile.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

using namespace monad;

// TinyVmPrecompile constructor creates the account with balance >= 1
// to survive EIP-161 empty account cleanup.
TEST(TinyVmPrecompile, constructor_creates_account_with_nonzero_balance)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    BlockState block_state{tdb, vm};
    BlockMetrics block_metrics;

    MonadDevnet chain;
    auto const genesis_state = chain.get_genesis_state();
    auto result = block_state.apply_genesis(genesis_state);
    ASSERT_TRUE(result.has_value());

    auto &state = block_state.state();
    trace::CallTracer tracer;

    // 0x420 should NOT exist before precompile construction
    EXPECT_EQ(state.get_balance(TINYVM_PRECOMPILE_ADDRESS), 0u);

    // Construct precompile — should create account
    TinyVmPrecompile precompile(state, tracer);

    EXPECT_GE(state.get_balance(TINYVM_PRECOMPILE_ADDRESS), 1u)
        << "precompile must fund 0x420 with at least 1 wei to survive EIP-161";
}
