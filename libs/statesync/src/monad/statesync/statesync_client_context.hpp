#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/db.hpp>

#include <filesystem>
#include <vector>

struct monad_statesync_client;
struct monad_sync_request;

MONAD_NAMESPACE_BEGIN

struct byte_string_hash
{
    using is_transparent = void;
    using is_avalanching = void;

    uint64_t operator()(byte_string_view const str) const
    {
        return ankerl::unordered_dense::hash<byte_string_view>{}(str);
    }
};

template <class V>
using ByteStringMap = ankerl::unordered_dense::segmented_map<
    byte_string, V, byte_string_hash, std::equal_to<>>;

struct SyncEntry
{
    byte_string value;
    bool incarnation;
    ByteStringMap<byte_string> storage;
};

using SyncState = ByteStringMap<SyncEntry>;

using SyncCode = ankerl::unordered_dense::segmented_map<
    monad::bytes32_t, monad::byte_string>;

MONAD_NAMESPACE_END

struct monad_statesync_client_context
{
    monad::OnDiskMachine machine;
    monad::mpt::Db db;
    std::vector<uint64_t> progress;
    uint8_t prefix_bytes;
    uint64_t target;
    uint64_t current;
    monad::bytes32_t expected_root;
    monad::SyncState state;
    monad::SyncCode code;
    std::unordered_set<monad::bytes32_t> hash;
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
