// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/execution/domain/statesync.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <initializer_list>
#include <limits>
#include <map>
#include <memory>
#include <optional>
#include <span>
#include <utility>

#include <sys/socket.h>
#include <sys/types.h>

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint32_t MAGIC = 0x4d445353; // "MDSS"
constexpr uint32_t VERSION = 1;
constexpr size_t REQUEST_SIZE = 4 + 4 + 8 + 8;

// Frame tags.
constexpr uint8_t FRAME_DATA = 1;
constexpr uint8_t FRAME_DONE = 2;
constexpr uint8_t FRAME_FAILED = 3;
constexpr size_t FRAME_HEADER_SIZE = 1 + 1 + 2 + 4;
// A snapshot record is at most a contract's code or one storage page.
constexpr uint32_t MAX_FRAME_SIZE = 1 << 26;

constexpr unsigned NO_SQ_THREAD = std::numeric_limits<unsigned>::max();
constexpr unsigned DUMP_CONCURRENCY = 64;
// The headers a snapshot carries: the block's and the 255 before it.
constexpr uint64_t SNAPSHOT_HEADERS = 256;

Result<void> send_all(int const fd, std::span<uint8_t const> bytes)
{
    while (!bytes.empty()) {
        ssize_t const sent =
            ::send(fd, bytes.data(), bytes.size(), MSG_NOSIGNAL);
        if (sent < 0 && errno == EINTR) {
            continue;
        }
        if (sent <= 0) {
            return StatesyncError::Connection;
        }
        bytes = bytes.subspan(static_cast<size_t>(sent));
    }
    return outcome::success();
}

Result<void> receive_all(int const fd, std::span<uint8_t> bytes)
{
    while (!bytes.empty()) {
        ssize_t const received = ::recv(fd, bytes.data(), bytes.size(), 0);
        if (received < 0 && errno == EINTR) {
            continue;
        }
        if (received <= 0) {
            return StatesyncError::Connection;
        }
        bytes = bytes.subspan(static_cast<size_t>(received));
    }
    return outcome::success();
}

Result<void> send_frame(
    int const fd, uint8_t const tag, uint8_t const type, uint16_t const shard,
    std::span<uint8_t const> const payload)
{
    std::array<uint8_t, FRAME_HEADER_SIZE> header{};
    header[0] = tag;
    header[1] = type;
    header[2] = static_cast<uint8_t>(shard >> 8);
    header[3] = static_cast<uint8_t>(shard);
    auto const length = static_cast<uint32_t>(payload.size());
    header[4] = static_cast<uint8_t>(length >> 24);
    header[5] = static_cast<uint8_t>(length >> 16);
    header[6] = static_cast<uint8_t>(length >> 8);
    header[7] = static_cast<uint8_t>(length);
    BOOST_OUTCOME_TRY(send_all(fd, header));
    return send_all(fd, payload);
}

// Where a dump writes its records: onto the socket, until a send fails.
struct DumpSink
{
    int fd;
    bool failed{false};
};

uint64_t write_snapshot_record(
    uint64_t const shard, monad_snapshot_type const type,
    unsigned char const *const bytes, size_t const len, void *const user)
{
    auto &sink = *static_cast<DumpSink *>(user);
    MONAD_ASSERT(shard < MONAD_SNAPSHOT_SHARDS);
    // The dump asserts that every record is written, so once a send fails the
    // rest are dropped here and the failure is reported when it returns.
    for (size_t offset = 0; offset < len && !sink.failed;) {
        size_t const size = std::min<size_t>(len - offset, MAX_FRAME_SIZE);
        sink.failed = send_frame(
                          sink.fd,
                          FRAME_DATA,
                          static_cast<uint8_t>(type),
                          static_cast<uint16_t>(shard),
                          {bytes + offset, size})
                          .has_error();
        offset += size;
    }
    return len;
}

// The streams of one snapshot shard, by monad_snapshot_type.
using ShardStreams = std::array<byte_string, MONAD_SNAPSHOT_FILES_PER_SHARD>;

// Receives a reply's data frames up to its end frame.
Result<std::map<uint16_t, ShardStreams>> receive_snapshot(int const fd)
{
    std::map<uint16_t, ShardStreams> shards;
    while (true) {
        std::array<uint8_t, FRAME_HEADER_SIZE> header{};
        BOOST_OUTCOME_TRY(receive_all(fd, header));
        uint8_t const tag = header[0];
        uint8_t const type = header[1];
        auto const shard = static_cast<uint16_t>((header[2] << 8) | header[3]);
        uint32_t const length = load_be_unsafe<uint32_t>(header.data() + 4);
        if (tag == FRAME_DONE) {
            return shards;
        }
        if (tag == FRAME_FAILED) {
            return StatesyncError::Unavailable;
        }
        if (tag != FRAME_DATA || type >= MONAD_SNAPSHOT_FILES_PER_SHARD ||
            shard >= MONAD_SNAPSHOT_SHARDS || length > MAX_FRAME_SIZE) {
            return StatesyncError::Protocol;
        }
        auto &stream = shards[shard][type];
        size_t const size = stream.size();
        stream.resize(size + length);
        BOOST_OUTCOME_TRY(receive_all(fd, {stream.data() + size, length}));
    }
}

// The header of finalized block `number` of `db`, and its hash.
std::optional<std::pair<BlockHeader, bytes32_t>>
read_header(mpt::Db const &db, uint64_t const number)
{
    auto const cursor = db.find(
        mpt::concat(FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
        number);
    if (cursor.has_error()) {
        return std::nullopt;
    }
    byte_string_view const encoded{cursor.value().node->value()};
    byte_string_view rest{encoded};
    auto header = rlp::decode_block_header(rest);
    if (header.has_error()) {
        return std::nullopt;
    }
    return std::pair{std::move(header).value(), to_bytes(keccak256(encoded))};
}

// Checks the db a snapshot of block `number` was loaded into against the
// block's attested hash.
Result<void> verify_domain_state(
    mpt::Db &db, uint64_t const number, bytes32_t const &block_hash)
{
    auto const block = read_header(db, number);
    if (!block.has_value() || block->first.number != number ||
        block->second != block_hash) {
        return StatesyncError::WrongBlockHash;
    }
    TrieDb state{db};
    state.set_block_and_prefix(number);
    if (state.state_root() != block->first.state_root) {
        return StatesyncError::WrongStateRoot;
    }
    // The state holds the hash of every block before this one, back to the
    // history's length. The headers before it are what BLOCKHASH and the
    // next block's parent hash would otherwise be taken from on trust.
    auto const history = state.read_account(BLOCK_HISTORY_ADDRESS);
    uint64_t const first =
        number < SNAPSHOT_HEADERS ? 0 : number - (SNAPSHOT_HEADERS - 1);
    for (uint64_t earlier = first; earlier < number; ++earlier) {
        auto const header = read_header(db, earlier);
        if (!header.has_value() || !history.has_value() ||
            header->first.number != earlier ||
            header->second != state.read_storage(
                                  BLOCK_HISTORY_ADDRESS,
                                  history->incarnation,
                                  bytes32_t{earlier % BLOCK_HISTORY_LENGTH})) {
            return StatesyncError::WrongBlockHistory;
        }
    }
    return outcome::success();
}

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

Result<void> serve_domain_state(
    int const fd, uint64_t const domain_chain_id,
    std::filesystem::path const &domain_db_path)
{
    std::array<uint8_t, REQUEST_SIZE> request{};
    BOOST_OUTCOME_TRY(receive_all(fd, request));
    if (load_be_unsafe<uint32_t>(request.data()) != MAGIC ||
        load_be_unsafe<uint32_t>(request.data() + 4) != VERSION) {
        return StatesyncError::Protocol;
    }
    if (load_be_unsafe<uint64_t>(request.data() + 8) != domain_chain_id) {
        BOOST_OUTCOME_TRY(send_frame(fd, FRAME_FAILED, 0, 0, {}));
        return StatesyncError::WrongDomain;
    }
    uint64_t const block = load_be_unsafe<uint64_t>(request.data() + 16);

    DumpSink sink{.fd = fd};
    bool const dumped = monad_db_dump_snapshot(
        domain_db_path.c_str(),
        NO_SQ_THREAD,
        block,
        write_snapshot_record,
        &sink,
        DUMP_CONCURRENCY,
        1,
        0,
        false,
        MONAD_SNAPSHOT_FORMAT_V2);
    if (sink.failed) {
        return StatesyncError::Connection;
    }
    BOOST_OUTCOME_TRY(
        send_frame(fd, dumped ? FRAME_DONE : FRAME_FAILED, 0, 0, {}));
    if (!dumped) {
        return StatesyncError::Unavailable;
    }
    return outcome::success();
}

Result<void> sync_domain_state(
    int const fd, uint64_t const domain_chain_id, uint64_t const block_number,
    bytes32_t const &block_hash, mpt::OnDiskDbConfig const &db_config)
{
    std::array<uint8_t, REQUEST_SIZE> request{};
    request[0] = static_cast<uint8_t>(MAGIC >> 24);
    request[1] = static_cast<uint8_t>(MAGIC >> 16);
    request[2] = static_cast<uint8_t>(MAGIC >> 8);
    request[3] = static_cast<uint8_t>(MAGIC);
    request[7] = static_cast<uint8_t>(VERSION);
    store_be(request.data() + 8, domain_chain_id);
    store_be(request.data() + 16, block_number);
    BOOST_OUTCOME_TRY(send_all(fd, request));
    BOOST_OUTCOME_TRY(auto const shards, receive_snapshot(fd));

    // The loader fills an empty db whose encoding is already set. A domain's
    // db is page-encoded.
    {
        mpt::OnDiskDbConfig create_config{db_config};
        create_config.append = false;
        mpt::Db const created{
            std::make_unique<MonadOnDiskMachine>(), create_config};
    }
    auto *const loader = monad_db_snapshot_loader_create(
        block_number,
        db_config.dbname_path.c_str(),
        db_config.sq_thread_cpu.value_or(NO_SQ_THREAD),
        false);
    for (auto const &[shard, streams] : shards) {
        auto const data = [&streams](monad_snapshot_type const type) {
            return streams[type].empty() ? nullptr : streams[type].data();
        };
        monad_db_snapshot_loader_load(
            loader,
            shard,
            data(MONAD_SNAPSHOT_ETH_HEADER),
            streams[MONAD_SNAPSHOT_ETH_HEADER].size(),
            data(MONAD_SNAPSHOT_ACCOUNT),
            streams[MONAD_SNAPSHOT_ACCOUNT].size(),
            data(MONAD_SNAPSHOT_STORAGE),
            streams[MONAD_SNAPSHOT_STORAGE].size(),
            data(MONAD_SNAPSHOT_CODE),
            streams[MONAD_SNAPSHOT_CODE].size());
    }
    monad_db_snapshot_loader_destroy(loader);

    mpt::OnDiskDbConfig open_config{db_config};
    open_config.append = true;
    mpt::Db db{open_config};
    return verify_domain_state(db, block_number, block_hash);
}

MONAD_DOMAIN_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::domain::StatesyncError>::mapping> const &
quick_status_code_from_enum<monad::domain::StatesyncError>::value_mappings()
{
    using monad::domain::StatesyncError;

    static std::initializer_list<mapping> const mappings = {
        {StatesyncError::Success, "success", {errc::success}},
        {StatesyncError::Connection,
         "the statesync connection failed or was closed early",
         {}},
        {StatesyncError::Protocol,
         "the statesync peer does not follow the protocol",
         {}},
        {StatesyncError::WrongDomain,
         "the statesync request is for another domain",
         {}},
        {StatesyncError::Unavailable,
         "the statesync peer cannot serve the block",
         {}},
        {StatesyncError::WrongBlockHash,
         "the block's header does not hash to the attested block hash",
         {}},
        {StatesyncError::WrongStateRoot,
         "the state does not have the state root of the block's header",
         {}},
        {StatesyncError::WrongBlockHistory,
         "an earlier block's header does not match the hash the state holds "
         "for it",
         {}}};
    return mappings;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
