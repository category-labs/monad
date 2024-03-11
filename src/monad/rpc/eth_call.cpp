#include <monad/core/block.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/read_only_trie_db.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/mpt/read_only_db.hpp>
#include <monad/rpc/eth_call.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/try.hpp>

MONAD_RPC_NAMESPACE_BEGIN

/*
    For eth_call with real txn, submit as it is
    For eth_call with only "from" "to" and "data", set txn.value = 0 & gas_limit
    to a big number to guarantee success on txn side if no "from", set from =
    "0x0000...00"
*/
Result<evmc::Result> eth_call(
    Transaction const &txn, BlockHeader const &header, uint64_t const block_id,
    Address const sender, BlockHashBuffer const &buffer,
    std::vector<std::filesystem::path> const &dbname_paths)
{
    // TODO: Hardset rev to be Shanghai at the moment
    static constexpr auto rev = EVMC_SHANGHAI;
    BOOST_OUTCOME_TRY(
        eth_call_static_validate_transaction<rev>(txn, header.base_fee_per_gas))

    mpt::ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = dbname_paths};
    db::ReadOnlyTrieDb ro_trie_db{ro_config, block_id};
    BlockState block_state{ro_trie_db};
    State state{block_state};

    auto const sender_account = state.recent_account(sender);
    BOOST_OUTCOME_TRY(eth_call_validate_transaction(txn, sender_account));

    auto const tx_context = get_tx_context<rev>(txn, sender, header);
    EvmcHost<rev> host{tx_context, buffer, state};

    return execute_impl_no_validation<rev>(
        state,
        host,
        txn,
        sender,
        header.base_fee_per_gas.value_or(0),
        header.beneficiary);
}

MONAD_RPC_NAMESPACE_END
