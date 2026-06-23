// Copyright (C) 2025 Category Labs, Inc.
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

#ifdef MONAD_HAVE_ROCKSDB

    #include <category/core/assert.h>
    #include <category/core/blake3.hpp>
    #include <category/core/byte_string.hpp>
    #include <category/core/bytes.hpp>
    #include <category/core/hex.hpp>
    #include <category/core/keccak.hpp>
    #include <category/execution/ethereum/core/account.hpp>
    #include <category/execution/ethereum/core/block.hpp>
    #include <category/execution/ethereum/core/rlp/block_rlp.hpp>
    #include <category/execution/ethereum/db/rocksdb_db.hpp>
    #include <category/execution/ethereum/db/snapshot_loader.hpp>
    #include <category/execution/ethereum/db/util.hpp>
    #include <category/execution/ethereum/state2/state_deltas.hpp>
    #include <category/execution/ethereum/types/incarnation.hpp>
    #include <category/vm/code.hpp>

    #include <fcntl.h>
    #include <sys/mman.h>
    #include <unistd.h>

    #include <cstring>
    #include <filesystem>
    #include <fstream>
    #include <map>
    #include <memory>
    #include <optional>
    #include <span>
    #include <sstream>
    #include <unordered_map>

MONAD_NAMESPACE_BEGIN

namespace
{
    struct Mapped
    {
        int fd{-1};
        unsigned char const *data{nullptr};
        size_t size{0};
    };

    // mmap a per-shard file read-only and verify its sibling .blake3 checksum.
    Mapped map_file(std::filesystem::path const &file)
    {
        MONAD_ASSERT(std::filesystem::is_regular_file(file));
        int const fd = ::open(file.c_str(), O_RDONLY);
        MONAD_ASSERT(fd != -1);
        size_t const size = std::filesystem::file_size(file);
        unsigned char const *data = nullptr;
        if (size) {
            void *const m = ::mmap(nullptr, size, PROT_READ, MAP_SHARED, fd, 0);
            MONAD_ASSERT(m != MAP_FAILED);
            MONAD_ASSERT(::madvise(m, size, MADV_SEQUENTIAL) == 0);
            std::filesystem::path const checksum{file.string() + ".blake3"};
            MONAD_ASSERT(std::filesystem::is_regular_file(checksum));
            std::ifstream t{checksum};
            std::stringstream buffer;
            buffer << t.rdbuf();
            auto const stored_hash = from_hex<bytes32_t>(buffer.str());
            auto const calculated_hash = to_bytes(
                blake3({reinterpret_cast<unsigned char const *>(m), size}));
            MONAD_ASSERT(stored_hash == calculated_hash);
            data = reinterpret_cast<unsigned char const *>(m);
        }
        return Mapped{.fd = fd, .data = data, .size = size};
    }

    void unmap(Mapped &m)
    {
        if (m.data) {
            ::munmap(const_cast<unsigned char *>(m.data), m.size);
        }
        if (m.fd != -1) {
            ::close(m.fd);
        }
    }

    struct AccountState
    {
        std::optional<Account> account;
        std::map<bytes32_t, bytes32_t> storage;
    };
}

bytes32_t seed_rocksdb_from_snapshot(
    std::filesystem::path const &snapshot_dir, uint64_t const block,
    std::filesystem::path const &rocksdb_dir)
{
    // The canonical dump layout is <snapshot_dir>/<block>/<shard>/, but a
    // transferred snapshot may have the shard directories sitting directly in
    // snapshot_dir (the block level flattened away). Accept either: prefer the
    // <block> subdirectory, else treat snapshot_dir itself as the shard parent.
    std::filesystem::path root{snapshot_dir / std::to_string(block)};
    if (!std::filesystem::is_directory(root)) {
        root = snapshot_dir;
    }
    MONAD_ASSERT(std::filesystem::is_directory(root));

    RocksDbDb db{rocksdb_dir};

    bytes32_t header_state_root{};
    bool found_header = false;

    // Stream shard by shard. Each shard's accounts + their storage (linked by
    // the in-shard account_offset) + code are decoded into one chunk and folded
    // into the on-disk trie via seed_chunk -- so peak memory is one shard's
    // worth, not the whole state. MPT insertion is order-independent, so the
    // shards can be processed in any order and still reproduce the same root.
    for (auto const &dir : std::filesystem::directory_iterator{root}) {
        if (!dir.is_directory()) {
            continue; // skip stray files; shards are subdirectories
        }
        Mapped eth = map_file(dir.path() / "eth_header");
        Mapped acct = map_file(dir.path() / "account");
        Mapped stor = map_file(dir.path() / "storage");
        Mapped code = map_file(dir.path() / "code");

        std::map<Address, AccountState> shard_state;
        std::unordered_map<uint64_t, Address> offset_to_addr;

        // Accounts: offset (into this shard's account file) -> Address.
        if (acct.data) {
            byte_string_view av{acct.data, acct.size};
            while (!av.empty()) {
                uint64_t const offset = acct.size - av.size();
                auto const dec = decode_account_db(av);
                MONAD_ASSERT(!dec.has_error());
                auto const [addr, account] = dec.value();
                offset_to_addr.emplace(offset, addr);
                shard_state[addr].account = account;
            }
        }

        // Storage: each record is [account_offset(8B)][encode_storage_db]. The
        // compact slot/value are left-padded to 32 bytes.
        if (stor.data) {
            byte_string_view sv{stor.data, stor.size};
            while (!sv.empty()) {
                MONAD_ASSERT(sv.size() >= sizeof(uint64_t));
                uint64_t offset;
                std::memcpy(&offset, sv.data(), sizeof(offset));
                sv.remove_prefix(sizeof(offset));
                auto const dec = decode_storage_db_raw(sv);
                MONAD_ASSERT(!dec.has_error());
                bytes32_t const slot = to_bytes(dec.value().first);
                bytes32_t const value = to_bytes(dec.value().second);
                Address const &addr = offset_to_addr.at(offset);
                shard_state[addr].storage[slot] = value;
            }
        }

        // Code: each record is [size(8B)][bytes].
        Code shard_code;
        if (code.data) {
            byte_string_view cv{code.data, code.size};
            while (!cv.empty()) {
                MONAD_ASSERT(cv.size() >= sizeof(uint64_t));
                uint64_t size;
                std::memcpy(&size, cv.data(), sizeof(size));
                cv.remove_prefix(sizeof(size));
                MONAD_ASSERT(cv.size() >= size);
                byte_string_view const bytecode = cv.substr(0, size);
                shard_code.emplace(
                    to_bytes(keccak256(bytecode)),
                    vm::make_shared_intercode(std::span<uint8_t const>{
                        bytecode.data(), bytecode.size()}));
                cv.remove_prefix(size);
            }
        }

        // The per-shard header is block (N - shard); capture block N's root.
        if (eth.data) {
            byte_string_view ev{eth.data, eth.size};
            auto const header = rlp::decode_block_header(ev);
            MONAD_ASSERT(!header.has_error());
            if (header.value().number == block) {
                header_state_root = header.value().state_root;
                found_header = true;
            }
        }

        unmap(eth);
        unmap(acct);
        unmap(stor);
        unmap(code);

        // Fold this shard's accounts + storage into the on-disk trie. Flat
        // values come along (raw keys, no un-hashing); the trie is updated
        // incrementally so nothing accumulates across shards.
        auto deltas = std::make_unique<StateDeltas>();
        for (auto const &[addr, st] : shard_state) {
            MONAD_ASSERT(st.account.has_value());
            StateDelta d{.account = {std::nullopt, st.account}};
            for (auto const &[slot, value] : st.storage) {
                d.storage.emplace(slot, StorageDelta{bytes32_t{}, value});
            }
            deltas->emplace(addr, std::move(d));
        }
        db.seed_chunk(std::move(deltas), shard_code);
    }
    MONAD_ASSERT(found_header);

    // The seed gate (inside seed_finalize): the folded state_root must equal
    // block N's ETH_HEADER stateRoot. Then CF_META is persisted.
    db.seed_finalize(block, header_state_root);
    return header_state_root;
}

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
