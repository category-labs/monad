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
    #include <category/execution/ethereum/db/commit_builder.hpp>
    #include <category/execution/ethereum/db/partial_trie_db.hpp>
    #include <category/execution/ethereum/db/snapshot_loader.hpp>
    #include <category/execution/ethereum/db/util.hpp>
    #include <category/execution/ethereum/state2/state_deltas.hpp>
    #include <category/execution/ethereum/types/incarnation.hpp>
    #include <category/statedb/kv_store.hpp>
    #include <category/statedb/schema.hpp>
    #include <category/statedb/trie_node_store.hpp>

    #include <fcntl.h>
    #include <sys/mman.h>
    #include <unistd.h>

    #include <cstring>
    #include <fstream>
    #include <map>
    #include <memory>
    #include <optional>
    #include <sstream>
    #include <string_view>
    #include <unordered_map>

MONAD_NAMESPACE_BEGIN

namespace
{
    using statedb::Cf;

    byte_string meta_key_bytes(std::string_view const s)
    {
        return byte_string{
            reinterpret_cast<unsigned char const *>(s.data()), s.size()};
    }

    byte_string be64(uint64_t const v)
    {
        byte_string b;
        for (int shift = 56; shift >= 0; shift -= 8) {
            b.push_back(static_cast<unsigned char>((v >> shift) & 0xff));
        }
        return b;
    }

    // Flat keys -- mirror FlatStateMirror so the seeded store is
    // read-compatible with the F5 shadow / the future RocksDbDb read path.
    byte_string account_key(Address const &addr)
    {
        return byte_string{addr.bytes, sizeof(addr.bytes)};
    }

    byte_string storage_key(
        Address const &addr, Incarnation const incarnation,
        bytes32_t const &slot)
    {
        byte_string k;
        k.reserve(sizeof(addr.bytes) + sizeof(uint64_t) + sizeof(slot.bytes));
        k.append(addr.bytes, sizeof(addr.bytes));
        uint64_t const inc = incarnation.to_int();
        for (int shift = 56; shift >= 0; shift -= 8) {
            k.push_back(static_cast<unsigned char>((inc >> shift) & 0xff));
        }
        k.append(slot.bytes, sizeof(slot.bytes));
        return k;
    }

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
    std::filesystem::path const root{snapshot_dir / std::to_string(block)};
    MONAD_ASSERT(std::filesystem::is_directory(root));

    auto kv = statedb::KvStore::open(rocksdb_dir);

    // Decode all shards into an in-memory model, capturing block N's header.
    std::map<Address, AccountState> state;
    bytes32_t header_state_root{};
    bool found_header = false;

    for (auto const &dir : std::filesystem::directory_iterator{root}) {
        Mapped eth = map_file(dir.path() / "eth_header");
        Mapped acct = map_file(dir.path() / "account");
        Mapped stor = map_file(dir.path() / "storage");
        Mapped code = map_file(dir.path() / "code");

        // Accounts: offset (into this shard's account file) -> Address.
        std::unordered_map<uint64_t, Address> offset_to_addr;
        if (acct.data) {
            byte_string_view av{acct.data, acct.size};
            while (!av.empty()) {
                uint64_t const offset = acct.size - av.size();
                auto const dec = decode_account_db(av);
                MONAD_ASSERT(!dec.has_error());
                auto const [addr, account] = dec.value();
                offset_to_addr.emplace(offset, addr);
                state[addr].account = account;
            }
        }

        // Storage: each record is [account_offset(8B)][encode_storage_db].
        if (stor.data) {
            byte_string_view sv{stor.data, stor.size};
            while (!sv.empty()) {
                MONAD_ASSERT(sv.size() >= sizeof(uint64_t));
                uint64_t offset;
                std::memcpy(&offset, sv.data(), sizeof(offset));
                sv.remove_prefix(sizeof(offset));
                // decode_storage_db_raw advances `sv` by one record (it does
                // not require the view to end here, unlike decode_storage_db);
                // the slot/value come back compact, so left-pad to 32 bytes.
                auto const dec = decode_storage_db_raw(sv);
                MONAD_ASSERT(!dec.has_error());
                bytes32_t const slot = to_bytes(dec.value().first);
                bytes32_t const value = to_bytes(dec.value().second);
                Address const &addr = offset_to_addr.at(offset);
                state[addr].storage[slot] = value;
            }
        }

        // Code: each record is [size(8B)][bytes]; written straight to CF_CODE.
        if (code.data) {
            byte_string_view cv{code.data, code.size};
            while (!cv.empty()) {
                MONAD_ASSERT(cv.size() >= sizeof(uint64_t));
                uint64_t size;
                std::memcpy(&size, cv.data(), sizeof(size));
                cv.remove_prefix(sizeof(size));
                MONAD_ASSERT(cv.size() >= size);
                byte_string_view const bytecode = cv.substr(0, size);
                bytes32_t const code_hash = to_bytes(keccak256(bytecode));
                kv->put(Cf::code, code_hash, bytecode);
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
    }
    MONAD_ASSERT(found_header);

    // Build StateDeltas + write the flat CFs (raw keys, no un-hashing).
    StateDeltas deltas;
    for (auto const &[addr, st] : state) {
        MONAD_ASSERT(st.account.has_value());
        StateDelta d{.account = {std::nullopt, st.account}};
        for (auto const &[slot, value] : st.storage) {
            d.storage.emplace(slot, StorageDelta{bytes32_t{}, value});
        }
        deltas.emplace(addr, d);

        kv->put(
            Cf::flat_state,
            account_key(addr),
            encode_account_db(addr, *st.account));
        for (auto const &[slot, value] : st.storage) {
            kv->put(
                Cf::flat_state,
                storage_key(addr, st.account->incarnation, slot),
                encode_storage_db(slot, value));
        }
    }

    // Build the canonical-RLP trie and compute the state root via
    // PartialTrieDb.
    auto pt = PartialTrieDb::from_witness(NULL_ROOT, {}, {});
    MONAD_ASSERT(!pt.has_error());
    CommitBuilder builder{block};
    pt.value().commit(
        bytes32_t{},
        builder,
        BlockHeader{.number = block},
        std::make_unique<StateDeltas>(std::move(deltas)),
        [](BlockHeader &) {});
    bytes32_t const state_root = pt.value().state_root();

    // The seed gate: the converted state root must equal block N's stateRoot.
    MONAD_ASSERT(state_root == header_state_root);

    // Emit the trie nodes to CF_TRIE_NODES.
    statedb::TrieNodeStore nodes{*kv, 1u << 16};
    pt.value().for_each_node(
        [&](bytes32_t const &node_hash, byte_string_view const rlp) {
            nodes.put(node_hash, rlp);
        });

    // CF_META: schema version, finalized base height, and the state root.
    kv->put(
        Cf::meta,
        meta_key_bytes(statedb::meta_key::schema_version),
        be64(statedb::SCHEMA_VERSION));
    kv->put(
        Cf::meta, meta_key_bytes(statedb::meta_key::finalized), be64(block));
    kv->put(
        Cf::meta, meta_key_bytes(statedb::meta_key::state_root), state_root);

    return state_root;
}

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
