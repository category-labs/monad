#include <monad/core/concepts.hpp>

#include <monad/db/block_db.hpp>
#include <monad/db/in_memory_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>
#include <monad/execution/static_precompiles.hpp>
#include <monad/execution/transaction_processor.hpp>

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
static constexpr auto o = 0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5_address;

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

TEST(TxnProcEvmInterpStateHost, account_transfer_miner_ommer_award)
{
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    state::AccountState accounts{db};
    state::ValueState values{db};
    code_db_t code_db{};
    state::CodeState codes{code_db};
    state::State s{accounts, values, codes, blocks, db};

    db.commit(state::StateChanges{
        .account_changes =
            {{a, Account{}}, // 'to' doesn't previously exist
             {from, Account{.balance = 10'000'000}}},
        .storage_changes = {}});

    BlockHeader const bh{.number = 2, .beneficiary = a};
    BlockHeader const ommer{.number = 1, .beneficiary = o};
    Transaction const t{
        .nonce = 0,
        .gas_price = 10,
        .gas_limit = 25'000,
        .amount = 1'000'000,
        .to = to,
        .from = from,
        .type = Transaction::Type::eip155};
    Block const b{.header = bh, .transactions = {t}, .ommers = {ommer}};

    auto changeset = s.get_new_changeset(0u);

    using state_t = decltype(changeset);
    using fork_t = monad::fork_traits::byzantium;
    using tp_t = execution::TransactionProcessor<state_t, fork_t>;

    tp_t tp{};
    evm_host_t<state_t, fork_t> h{bh, t, changeset};

    EXPECT_EQ(tp.validate(changeset, t, 0), tp_t::Status::SUCCESS);

    auto r = tp.execute(changeset, h, t, 0);
    EXPECT_EQ(r.status, Receipt::Status::SUCCESS);
    EXPECT_EQ(r.gas_used, 21'000);
    EXPECT_EQ(t.type, Transaction::Type::eip155);
    EXPECT_EQ(changeset.get_balance(from), bytes32_t{8'790'000});
    EXPECT_EQ(changeset.get_balance(to), bytes32_t{1'000'000});

    EXPECT_EQ(
        s.can_merge_changes(changeset),
        decltype(s)::MergeStatus::WILL_SUCCEED);
    s.merge_changes(changeset);

    fork_t::apply_block_award(s, b);

    auto ws = s.get_new_changeset(1u);
    ws.access_account(a);
    ws.access_account(o);
    EXPECT_EQ(ws.get_balance(a), bytes32_t{3'093'750'000'000'210'000});
    EXPECT_EQ(ws.get_balance(o), bytes32_t{2'625'000'000'000'000'000});
}

TEST(TxnProcEvmInterpStateHost, out_of_gas_account_creation_failure)
{
    // Block 46'402, txn 0
    static constexpr auto creator = 0xA1E4380A3B1f749673E270229993eE55F35663b4_address;
    static constexpr auto created = 0x9a049f5d18c239efaa258af9f3e7002949a977a0_address;
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    state::AccountState accounts{db};
    state::ValueState values{db};
    code_db_t code_db{};
    state::CodeState codes{code_db};
    state::State s{accounts, values, codes, blocks, db};

    db.commit(state::StateChanges{
        .account_changes =
            {{a, Account{}},
             {creator, Account{.balance = 9'000'000'000'000'000'000, .nonce = 3}}},
        .storage_changes = {}});

    byte_string code = {0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x00, 0x80, 0x54,
                        0x60, 0x01, 0x60, 0xa0, 0x60, 0x02, 0x0a, 0x03, 0x19,
                        0x16, 0x33, 0x17, 0x90, 0x55, 0x60, 0x06, 0x80, 0x60,
                        0x23, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3, 0x00, 0x60,
                        0x60, 0x60, 0x40, 0x52, 0x00};
    BlockHeader const bh{.number = 2, .beneficiary = a};
    Transaction const t{
        .nonce = 3,
        .gas_price = 10'000'000'000'000, // 10'000 GWei
        .gas_limit = 24'000,
        .amount = 0,
        .from = creator,
        .data = code,
        .type = Transaction::Type::eip155};
    Block const b{.header = bh, .transactions = {t}};

    auto changeset = s.get_new_changeset(0u);

    using state_t = decltype(changeset);
    using fork_t = monad::fork_traits::frontier;
    using tp_t = execution::TransactionProcessor<state_t, fork_t>;

    tp_t tp{};
    evm_host_t<state_t, fork_t> h{bh, t, changeset};

    EXPECT_EQ(tp.validate(changeset, t, 0), tp_t::Status::SUCCESS);

    auto r = tp.execute(changeset, h, t, 0);
    EXPECT_EQ(r.status, Receipt::Status::FAILED);
    EXPECT_EQ(r.gas_used, 24'000);
    EXPECT_EQ(t.type, Transaction::Type::eip155);
    EXPECT_EQ(changeset.get_balance(creator), bytes32_t{8'760'000'000'000'000'000});
    EXPECT_EQ(changeset.get_balance(created), bytes32_t{0});

    EXPECT_EQ(
        s.can_merge_changes(changeset),
        decltype(s)::MergeStatus::WILL_SUCCEED);
    s.merge_changes(changeset);

    fork_t::apply_block_award(s, b);

    auto ws = s.get_new_changeset(1u);
    ws.access_account(a);
    ws.access_account(o);
    EXPECT_EQ(ws.get_balance(a), bytes32_t{5'240'000'000'000'000'000});
}
