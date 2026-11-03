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

#include <category/core/assert.h>
#include <category/core/blocked_bloom_filter.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/log.hpp>
#include <category/crypto/hash256.h>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/db/storage_filter.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/util.hpp>

#include <komihash.h>

#include <fcntl.h>
#include <pthread.h>
#include <sys/stat.h>
#include <unistd.h>

#include <algorithm>
#include <atomic>
#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <filesystem>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <thread>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

uint64_t load_u64(unsigned char const *const p) noexcept
{
    uint64_t v;
    std::memcpy(&v, p, sizeof(v));
    return v;
}

// The two halves of the bloom key. Both trie path halves are keccak outputs;
// combining them keeps the keys of one account, and the same slot of many
// accounts, spread over the whole filter.
uint64_t h1(monad_hash256 const &a, monad_hash256 const &k) noexcept
{
    return load_u64(a.bytes) ^ load_u64(k.bytes);
}

uint64_t h2(monad_hash256 const &a, monad_hash256 const &k) noexcept
{
    return load_u64(a.bytes + 8) ^ load_u64(k.bytes + 8);
}

// File layout: this header, then the filter's bits, in native byte order.
struct FileHeader
{
    char magic[8];
    uint32_t format;
    uint32_t num_probes;
    uint64_t num_blocks;
    uint64_t block_number;
    unsigned char state_root[32];
    uint8_t page_encoded;
    uint8_t pad[7];
    uint64_t checksum; // komihash (streamed) of the bits, seed 0
};

static_assert(sizeof(FileHeader) == 80);

constexpr char FILE_MAGIC[8] = {'M', 'O', 'N', 'A', 'D', 'S', 'F', 'L'};
constexpr uint32_t FILE_FORMAT = 1;

// Saving copies and hashes the bits 1 MiB at a time
constexpr size_t CHUNK_WORDS = (size_t{1} << 20) / sizeof(uint64_t);

bool write_all(int const fd, void const *const data, size_t size) noexcept
{
    auto const *p = static_cast<unsigned char const *>(data);
    while (size > 0) {
        ssize_t const n = ::write(fd, p, size);
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            return false;
        }
        p += n;
        size -= static_cast<size_t>(n);
    }
    return true;
}

bool read_all(int const fd, void *const data, size_t size) noexcept
{
    auto *p = static_cast<unsigned char *>(data);
    while (size > 0) {
        ssize_t const n = ::read(fd, p, size);
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            return false;
        }
        if (n == 0) {
            return false;
        }
        p += n;
        size -= static_cast<size_t>(n);
    }
    return true;
}

// Inserts the storage leaves below the state table root. A storage leaf is
// a node with a value 128 nibbles below the root: keccak(address) followed
// by keccak(slot) on a slot-encoded db, keccak(page key) on a page-encoded
// one. Only subtries whose first two nibbles are in the given sets are
// visited. Clones share the leaf count; a traversal runs on one thread.
class StorageLeafInserter final : public mpt::TraverseMachine
{
    static constexpr unsigned LEAF_DEPTH = 128;

    StorageFilter *filter_;
    uint16_t first_nibbles_;
    uint16_t second_nibbles_;
    std::atomic<bool> const *stop_;
    uint64_t *leaves_;
    unsigned depth_{0};
    unsigned char path_[LEAF_DEPTH]{};

    bool in_sets(unsigned const depth, unsigned const nibble) const noexcept
    {
        uint16_t const set = depth == 0 ? first_nibbles_ : second_nibbles_;
        return depth > 1 || (set & (1u << nibble)) != 0;
    }

public:
    StorageLeafInserter(
        StorageFilter &filter, uint16_t const first_nibbles,
        uint16_t const second_nibbles, std::atomic<bool> const *const stop,
        uint64_t &leaves)
        : filter_{&filter}
        , first_nibbles_{first_nibbles}
        , second_nibbles_{second_nibbles}
        , stop_{stop}
        , leaves_{&leaves}
    {
    }

    bool should_visit(mpt::Node const &, unsigned char const branch) override
    {
        return in_sets(depth_, branch);
    }

    // Returning false skips the node's subtrie, and then up() is not called
    // for it
    bool down(unsigned char const branch, mpt::Node const &node) override
    {
        if (stop_ != nullptr && stop_->load(std::memory_order_relaxed)) {
            return false;
        }
        if (branch == mpt::INVALID_BRANCH) {
            MONAD_ASSERT(node.path_nibble_view().nibble_size() == 0);
            return true;
        }
        auto const path = node.path_nibble_view();
        MONAD_ASSERT(depth_ + 1 + path.nibble_size() <= LEAF_DEPTH);
        unsigned const depth = depth_;
        path_[depth_++] = branch;
        for (unsigned i = 0; i < path.nibble_size(); ++i) {
            path_[depth_++] = path.get(i);
        }
        // The second nibble can be part of this node's path rather than a
        // branch that should_visit sees
        if (depth == 0 && depth_ > 1 && !in_sets(1, path_[1])) {
            depth_ = depth;
            return false;
        }
        if (depth_ == LEAF_DEPTH && node.has_value()) {
            monad_hash256 address_hash;
            monad_hash256 key_hash;
            for (unsigned j = 0; j < sizeof(address_hash.bytes); ++j) {
                address_hash.bytes[j] = static_cast<uint8_t>(
                    (path_[2 * j] << 4) | path_[2 * j + 1]);
                key_hash.bytes[j] = static_cast<uint8_t>(
                    (path_[64 + 2 * j] << 4) | path_[64 + 2 * j + 1]);
            }
            filter_->insert(address_hash, key_hash);
            ++*leaves_;
        }
        return true;
    }

    void up(unsigned char const branch, mpt::Node const &node) override
    {
        if (branch == mpt::INVALID_BRANCH) {
            return;
        }
        depth_ -= 1 + node.path_nibble_view().nibble_size();
    }

    std::unique_ptr<mpt::TraverseMachine> clone() const override
    {
        return std::make_unique<StorageLeafInserter>(*this);
    }
};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

StorageFilter::Config
StorageFilter::default_config(bool const page_encoded) noexcept
{
    if (page_encoded) {
        return Config{.size_bytes = size_t{512} << 20, .num_probes = 8};
    }
    return Config{.size_bytes = size_t{2048} << 20, .num_probes = 6};
}

StorageFilter::StorageFilter(
    Config const &config, bool const page_encoded,
    uint64_t const base_block_number)
    : bloom_{BlockedBloomFilter::blocks_for_size(config.size_bytes), config.num_probes}
    , page_encoded_{page_encoded}
    , base_block_number_{base_block_number}
{
}

void StorageFilter::insert(
    monad_hash256 const &address_hash, monad_hash256 const &key_hash) noexcept
{
    bloom_.insert(h1(address_hash, key_hash), h2(address_hash, key_hash));
}

bool StorageFilter::may_contain(
    monad_hash256 const &address_hash,
    monad_hash256 const &key_hash) const noexcept
{
    return bloom_.may_contain(
        h1(address_hash, key_hash), h2(address_hash, key_hash));
}

bool StorageFilter::save(
    std::filesystem::path const &path, StorageFilterTag const &tag) const
{
    MONAD_ASSERT(tag.page_encoded == page_encoded_);
    MONAD_ASSERT(tag.block_number >= base_block_number_);
    FileHeader header{};
    std::memcpy(header.magic, FILE_MAGIC, sizeof(header.magic));
    header.format = FILE_FORMAT;
    header.num_probes = bloom_.num_probes();
    header.num_blocks = bloom_.num_blocks();
    header.block_number = tag.block_number;
    std::memcpy(
        header.state_root, tag.state_root.bytes, sizeof(header.state_root));
    header.page_encoded = page_encoded_ ? 1 : 0;

    // Written in full under a temporary name, then renamed over the target,
    // so the target is either the old file or the complete new one. The bits
    // are copied a chunk at a time, so blocks may keep inserting meanwhile.
    auto const tmp = std::filesystem::path{path.string() + ".tmp"};
    int const fd = ::open(tmp.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) {
        LOG_ERROR(
            "storage filter: cannot create {}: {}",
            tmp.string(),
            std::strerror(errno));
        return false;
    }
    bool ok = write_all(fd, &header, sizeof(header));
    komihash_stream_t hash;
    komihash_stream_init(&hash, 0);
    std::vector<uint64_t> chunk(CHUNK_WORDS);
    uint64_t const num_words = bloom_.num_words();
    for (uint64_t w = 0; ok && w < num_words; w += CHUNK_WORDS) {
        std::span<uint64_t> const part{
            chunk.data(), std::min<uint64_t>(CHUNK_WORDS, num_words - w)};
        bloom_.copy_words(w, part);
        komihash_stream_update(&hash, part.data(), part.size_bytes());
        ok = write_all(fd, part.data(), part.size_bytes());
    }
    header.checksum = komihash_stream_final(&hash);
    ok = ok &&
         ::pwrite(fd, &header, sizeof(header), 0) ==
             static_cast<ssize_t>(sizeof(header)) &&
         ::fdatasync(fd) == 0;
    int const saved_errno = errno;
    ::close(fd);
    std::error_code ec;
    if (ok) {
        std::filesystem::rename(tmp, path, ec);
    }
    if (!ok || ec) {
        LOG_ERROR(
            "storage filter: cannot write {}: {}",
            path.string(),
            ok ? ec.message() : std::strerror(saved_errno));
        std::filesystem::remove(tmp, ec);
        return false;
    }
    LOG_INFO(
        "storage filter: saved {} for block {}",
        path.string(),
        tag.block_number);
    return true;
}

std::unique_ptr<StorageFilter> StorageFilter::load(
    std::filesystem::path const &path, StorageFilterTag const &expected,
    Config const &config)
{
    int const fd = ::open(path.c_str(), O_RDONLY);
    if (fd < 0) {
        LOG_INFO(
            "storage filter: no file at {} ({})",
            path.string(),
            std::strerror(errno));
        return nullptr;
    }
    auto filter = std::make_unique<StorageFilter>(
        config, expected.page_encoded, expected.block_number);
    auto const reject = [&](std::string_view const why) {
        LOG_WARNING("storage filter: not using {}: {}", path.string(), why);
        ::close(fd);
        return nullptr;
    };
    FileHeader header;
    if (!read_all(fd, &header, sizeof(header)) ||
        std::memcmp(header.magic, FILE_MAGIC, sizeof(header.magic)) != 0 ||
        header.format != FILE_FORMAT) {
        return reject("not a storage filter file of this format");
    }
    if (header.num_probes != filter->bloom_.num_probes() ||
        header.num_blocks != filter->bloom_.num_blocks()) {
        return reject("saved with another size or number of probes");
    }
    if ((header.page_encoded != 0) != expected.page_encoded) {
        return reject("saved for another storage encoding");
    }
    if (header.block_number != expected.block_number) {
        return reject(
            "saved for block " + std::to_string(header.block_number) +
            ", the db is at block " + std::to_string(expected.block_number));
    }
    if (std::memcmp(
            header.state_root,
            expected.state_root.bytes,
            sizeof(header.state_root)) != 0) {
        return reject("saved for another state at this block");
    }
    struct stat st;
    auto const bits = filter->bloom_.bytes();
    if (::fstat(fd, &st) != 0 ||
        static_cast<uint64_t>(st.st_size) != sizeof(header) + bits.size()) {
        return reject("wrong file size");
    }
    if (!read_all(fd, bits.data(), bits.size())) {
        return reject("read failed");
    }
    ::close(fd);
    komihash_stream_t hash;
    komihash_stream_init(&hash, 0);
    for (size_t off = 0; off < bits.size(); off += CHUNK_WORDS * 8) {
        komihash_stream_update(
            &hash,
            bits.data() + off,
            std::min<size_t>(CHUNK_WORDS * 8, bits.size() - off));
    }
    if (komihash_stream_final(&hash) != header.checksum) {
        LOG_WARNING(
            "storage filter: not using {}: checksum mismatch", path.string());
        return nullptr;
    }
    filter->set_ready();
    LOG_INFO(
        "storage filter: loaded {} for block {}",
        path.string(),
        expected.block_number);
    return filter;
}

std::optional<StorageFilterTag> finalized_storage_filter_tag(
    mpt::Db &db, mpt::Node::SharedPtr const &root, uint64_t const block_number,
    bool const page_encoded)
{
    if (!root || !db.find(root, finalized_nibbles, block_number).has_value()) {
        return std::nullopt;
    }
    bytes32_t state_root = NULL_ROOT;
    auto const res = db.find(
        root, mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE), block_number);
    if (res.has_value() && !res.value().node->data().empty()) {
        auto const data = res.value().node->data();
        MONAD_ASSERT(data.size() == sizeof(bytes32_t));
        state_root = to_bytes(data);
    }
    return StorageFilterTag{
        .block_number = block_number,
        .state_root = state_root,
        .page_encoded = page_encoded};
}

std::optional<StorageFilterTag> finalized_storage_filter_tag(
    mpt::Db &db, uint64_t const block_number, bool const page_encoded)
{
    return finalized_storage_filter_tag(
        db, db.load_root_for_version(block_number), block_number, page_encoded);
}

std::optional<uint64_t> insert_storage_leaves(
    StorageFilter &filter, mpt::Db &db, mpt::Node::SharedPtr const &root,
    uint64_t const block_number, uint16_t const first_nibbles,
    uint16_t const second_nibbles, size_t const concurrency_limit,
    std::atomic<bool> const *const stop)
{
    if (!root || !db.find(root, finalized_nibbles, block_number).has_value()) {
        return std::nullopt;
    }
    auto const state = db.find(
        root, mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE), block_number);
    if (!state.has_value()) {
        return 0; // no accounts, so no storage
    }
    uint64_t leaves = 0;
    StorageLeafInserter machine{
        filter, first_nibbles, second_nibbles, stop, leaves};
    // A read-write on-disk db must not run a parallel traversal (it would
    // block its io thread); see TrieDb::to_json
    bool const ok =
        db.is_on_disk() && !db.is_read_only()
            ? db.traverse_blocking(state.value(), machine, block_number)
            : db.traverse(
                  state.value(), machine, block_number, concurrency_limit);
    if (!ok || (stop != nullptr && stop->load(std::memory_order_relaxed))) {
        return std::nullopt;
    }
    return leaves;
}

std::optional<uint64_t> build_storage_filter(
    StorageFilter &filter, std::filesystem::path const &dbname_path,
    uint64_t const block_number, unsigned num_threads,
    std::atomic<bool> const *const stop)
{
    constexpr unsigned CONCURRENCY = 1024;
    // The state trie is shared out as its 256 subtries below the first two
    // nibbles, taken in turn by whichever thread is free, so that threads
    // finish together
    constexpr unsigned PARTS = 256;
    num_threads = std::clamp(num_threads, 1u, 16u);
    std::atomic<unsigned> next_part{0};
    std::atomic<uint64_t> total{0};
    std::atomic<bool> failed{false};
    std::vector<std::thread> threads;
    threads.reserve(num_threads);
    for (unsigned t = 0; t < num_threads; ++t) {
        threads.emplace_back([&] {
            pthread_setname_np(pthread_self(), "storage filter");
            try {
                mpt::AsyncIOContext io_ctx{mpt::ReadOnlyOnDiskDbConfig{
                    .rd_buffers = 2 * CONCURRENCY,
                    .uring_entries = 512,
                    .dbname_path = dbname_path,
                    .concurrent_read_io_limit = CONCURRENCY}};
                mpt::Db db{io_ctx};
                auto const root = db.load_root_for_version(block_number);
                for (unsigned part = next_part.fetch_add(1);
                     part < PARTS && !failed.load();
                     part = next_part.fetch_add(1)) {
                    auto const leaves = insert_storage_leaves(
                        filter,
                        db,
                        root,
                        block_number,
                        static_cast<uint16_t>(1u << (part >> 4)),
                        static_cast<uint16_t>(1u << (part & 15)),
                        CONCURRENCY,
                        stop);
                    if (!leaves.has_value()) {
                        failed.store(true);
                        break;
                    }
                    total.fetch_add(leaves.value());
                }
            }
            catch (std::exception const &e) {
                LOG_ERROR("storage filter: build thread failed: {}", e.what());
                failed.store(true);
            }
        });
    }
    for (auto &thread : threads) {
        thread.join();
    }
    if (failed.load()) {
        return std::nullopt;
    }
    return total.load();
}

MONAD_NAMESPACE_END
