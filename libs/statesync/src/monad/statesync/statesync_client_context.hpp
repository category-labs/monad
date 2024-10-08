#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/db.hpp>

#include <ankerl/unordered_dense.h>

#include <filesystem>
#include <optional>
#include <utility>
#include <vector>

struct monad_statesync_client;
struct monad_sync_request;

struct monad_statesync_client_context
{
    template <class K, class V>
    using Map = ankerl::unordered_dense::segmented_map<K, V>;

    using StorageDeltas = Map<monad::bytes32_t, monad::bytes32_t>;

    using StateDelta = std::pair<monad::Account, StorageDeltas>;

    monad::OnDiskMachine machine;
    monad::mpt::Db db;
    monad::TrieDb tdb;
    std::vector<std::pair<uint64_t, uint64_t>> progress;
    uint8_t prefix_bytes;
    uint64_t target;
    uint64_t current;
    monad::bytes32_t expected_root;
    Map<monad::Address, StorageDeltas> buffered;
    Map<monad::bytes32_t, monad::byte_string> code;
    Map<monad::Address, std::optional<StateDelta>> deltas;
    ankerl::unordered_dense::segmented_set<monad::bytes32_t> hash;
    uint64_t n_upserts;
    std::filesystem::path genesis;
    monad_statesync_client *sync;
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request);

    monad_statesync_client_context(
        std::vector<std::filesystem::path> dbname_paths,
        std::filesystem::path genesis, uint8_t prefix_bytes,
        monad_statesync_client *,
        void (*statesync_send_request)(
            struct monad_statesync_client *, struct monad_sync_request));
};
