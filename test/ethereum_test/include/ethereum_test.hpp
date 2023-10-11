#pragma once

#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/state2/state.hpp>
#include <monad/test/config.hpp>

#include <nlohmann/json.hpp>

MONAD_TEST_NAMESPACE_BEGIN

using mutex_t = std::shared_mutex;

using db_t = monad::db::InMemoryTrieDB;
using state_t = monad::state::State<mutex_t, monad::execution::fake::BlockDb>;

template <typename TTraits>
using transaction_processor_t =
    monad::execution::TransactionProcessor<state_t, TTraits>;

template <typename TTraits>
using host_t = monad::execution::EvmcHost<state_t, TTraits>;

void load_state_from_json(nlohmann::json const &, state_t &);

MONAD_TEST_NAMESPACE_END
