#include <monad/core/concepts.hpp>

#include <monad/db/block_db.hpp>
#include <monad/db/in_memory_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/state_changes.hpp>
#include <monad/state/value_state.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <unordered_map>

using namespace monad;

static constexpr auto from = 0x5353535353535353535353535353535353535353_address;
static constexpr auto to = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto a = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;

using code_db_t = std::unordered_map<address_t, byte_string>;
using account_store_db_t = db::InMemoryDB;

template <class TState, concepts::fork_traits<TState> TTraits>
using traits_templated_static_precompiles_t = execution::StaticPrecompiles<
    TState, TTraits, typename TTraits::static_precompiles_t>;

template <class TState, concepts::fork_traits<TState> TTraits>
using evm_t = execution::Evm<
    TState, TTraits, traits_templated_static_precompiles_t<TState, TTraits>,
    execution::EVMOneBaselineInterpreter<TState, TTraits>>;

template <class TState, concepts::fork_traits<TState> TTraits>
using evm_host_t = execution::EvmcHost<TState, TTraits, evm_t<TState, TTraits>>;

TEST(TxnProcEvmInterpStateHost, account_transfer)
{
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    state::AccountState accounts{db};
    state::ValueState values{db};
    code_db_t code_db{};
    state::CodeState codes{code_db};
    state::State s{accounts, values, codes, blocks};

    db.commit(state::StateChanges{
        .account_changes =
            {{a, Account{}},
             {to, Account{}},
             {from, Account{.balance = 10'000'000}}},
        .storage_changes = {}});

    BlockHeader const b{.beneficiary = a};
    Transaction const t{
        .nonce = 0,
        .gas_price = 10,
        .gas_limit = 25'000,
        .amount = 1'000'000,
        .to = to,
        .from = from,
        .type = Transaction::Type::eip155};

    auto working_state = s.get_working_copy(0u);

    using state_t = decltype(working_state);
    using fork_t = monad::fork_traits::byzantium;

    execution::TransactionProcessor<state_t, fork_t> tp{};

    using tp_t = decltype(tp);

    EXPECT_EQ(tp.validate(working_state, t, 0), tp_t::Status::SUCCESS);

    evm_host_t<state_t, fork_t> h{b, t, working_state};

    auto r = tp.execute(working_state, h, t, 0);

    EXPECT_EQ(r.status, Receipt::Status::SUCCESS);
    EXPECT_EQ(r.gas_used, 21'000);
    EXPECT_EQ(t.type, Transaction::Type::eip155);
    EXPECT_EQ(working_state.get_balance(from), bytes32_t{8'790'000});
    EXPECT_EQ(working_state.get_balance(to), bytes32_t{1'000'000});
}
