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
    #include <category/core/byte_string.hpp>
    #include <category/core/bytes.hpp>
    #include <category/core/keccak.hpp>
    #include <category/core/log.hpp>
    #include <category/execution/ethereum/core/account.hpp>
    #include <category/execution/ethereum/core/block.hpp>
    #include <category/execution/ethereum/core/rlp/account_rlp.hpp>
    #include <category/execution/ethereum/db/commit_builder.hpp>
    #include <category/execution/ethereum/db/partial_trie_db.hpp>
    #include <category/execution/ethereum/db/rocksdb_db.hpp>
    #include <category/execution/ethereum/db/util.hpp>
    #include <category/execution/ethereum/rlp/decode.hpp>
    #include <category/execution/ethereum/state2/state_deltas.hpp>
    #include <category/execution/ethereum/types/incarnation.hpp>
    #include <category/mpt/db.hpp>
    #include <category/mpt/merkle/compact_encode.hpp>
    #include <category/mpt/nibbles_view.hpp>
    #include <category/mpt/node.hpp>
    #include <category/mpt/update.hpp>
    #include <category/statedb/kv_store.hpp>
    #include <category/statedb/schema.hpp>
    #include <category/vm/code.hpp>

    #include <rocksdb/iterator.h>
    #include <rocksdb/slice.h>
    #include <rocksdb/write_batch.h>

    #include <array>
    #include <chrono>
    #include <cstddef>
    #include <cstdint>
    #include <cstring>
    #include <memory>
    #include <optional>
    #include <set>
    #include <utility>

MONAD_NAMESPACE_BEGIN

using statedb::Cf;

struct RocksDbCommitTrace
{
    uint64_t block = 0;

    uint64_t total_us = 0;
    uint64_t build_us = 0;
    uint64_t local_roots_us = 0;
    uint64_t code_stage_us = 0;
    uint64_t state_chunk_us = 0;
    uint64_t witness_us = 0;
    uint64_t from_witness_us = 0;
    uint64_t flat_stage_us = 0;
    uint64_t trie_replay_us = 0;
    uint64_t trie_stage_us = 0;
    uint64_t populate_header_us = 0;
    uint64_t meta_stage_us = 0;
    uint64_t write_us = 0;

    std::size_t accounts = 0;
    std::size_t account_puts = 0;
    std::size_t account_deletes = 0;
    std::size_t incarnation_bumps = 0;
    std::size_t storage_deltas = 0;
    std::size_t storage_puts = 0;
    std::size_t storage_deletes = 0;
    std::size_t prefix_clears = 0;
    std::size_t prefix_delete_keys = 0;

    std::size_t account_descends = 0;
    std::size_t storage_descends = 0;
    std::size_t node_gets = 0;
    std::size_t node_hits = 0;
    std::size_t node_misses = 0;
    std::size_t sibling_prefetches = 0;
    std::size_t witness_seen_keys = 0;
    std::size_t witness_nodes = 0;
    std::size_t witness_bytes = 0;

    std::size_t code_candidates = 0;
    std::size_t code_puts = 0;
    std::size_t code_put_bytes = 0;
    std::size_t trie_node_puts = 0;
    std::size_t trie_node_put_bytes = 0;
    std::size_t batch_keys = 0;
    std::size_t batch_bytes = 0;
};

namespace
{
    using Clock = std::chrono::steady_clock;

    uint64_t elapsed_us(Clock::time_point const begin)
    {
        return static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(
                Clock::now() - begin)
                .count());
    }

    void log_commit_trace(RocksDbCommitTrace const &t)
    {
        LOG_INFO(
            "__rocksdb_commit,bl={},tot={}us,build={}us,local_roots={}us,"
            "code={}us,state={}us,witness={}us,from_witness={}us,flat={}us,"
            "trie_replay={}us,trie_stage={}us,pop_hdr={}us,meta={}us,"
            "write={}us,acct={},acct_put={},acct_del={},inc_bump={},"
            "stor={},stor_put={},stor_del={},prefix_clear={},"
            "prefix_del_keys={},w_acct={},w_stor={},node_get={},node_hit={},"
            "node_miss={},prefetch={},wit_seen={},wit_nodes={},wit_bytes={},"
            "code_candidates={},code_put={},code_put_bytes={},trie_put={},"
            "trie_put_bytes={},batch_keys={},batch_bytes={}",
            t.block,
            t.total_us,
            t.build_us,
            t.local_roots_us,
            t.code_stage_us,
            t.state_chunk_us,
            t.witness_us,
            t.from_witness_us,
            t.flat_stage_us,
            t.trie_replay_us,
            t.trie_stage_us,
            t.populate_header_us,
            t.meta_stage_us,
            t.write_us,
            t.accounts,
            t.account_puts,
            t.account_deletes,
            t.incarnation_bumps,
            t.storage_deltas,
            t.storage_puts,
            t.storage_deletes,
            t.prefix_clears,
            t.prefix_delete_keys,
            t.account_descends,
            t.storage_descends,
            t.node_gets,
            t.node_hits,
            t.node_misses,
            t.sibling_prefetches,
            t.witness_seen_keys,
            t.witness_nodes,
            t.witness_bytes,
            t.code_candidates,
            t.code_puts,
            t.code_put_bytes,
            t.trie_node_puts,
            t.trie_node_put_bytes,
            t.batch_keys,
            t.batch_bytes);
    }

    byte_string_view meta_bsv(std::string_view const s)
    {
        return byte_string_view{
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

    uint64_t decode_be64(byte_string_view const b)
    {
        uint64_t n = 0;
        for (unsigned char const byte : b) {
            n = (n << 8) | byte;
        }
        return n;
    }

    // Flat CF keys -- identical to FlatStateMirror / snapshot_loader so the
    // store stays read-compatible across the seed, the F5 shadow, and here.
    byte_string account_key(Address const &addr)
    {
        return byte_string{addr.bytes, sizeof(addr.bytes)};
    }

    byte_string storage_key(Address const &addr, bytes32_t const &slot)
    {
        byte_string k;
        k.reserve(sizeof(addr.bytes) + sizeof(slot.bytes));
        k.append(addr.bytes, sizeof(addr.bytes));
        k.append(slot.bytes, sizeof(slot.bytes));
        return k;
    }

    byte_string storage_seek_key(Address const &addr)
    {
        byte_string k{addr.bytes, sizeof(addr.bytes)};
        k.push_back(0);
        return k;
    }

    rocksdb::Slice to_slice(byte_string_view const v)
    {
        return rocksdb::Slice{
            reinterpret_cast<char const *>(v.data()), v.size()};
    }

    bool is_storage_key_for_address(
        rocksdb::Slice const &key, Address const &addr)
    {
        return key.size() > sizeof(addr.bytes) &&
               std::memcmp(key.data(), addr.bytes, sizeof(addr.bytes)) == 0;
    }

    byte_string to_byte_string(rocksdb::Slice const &key)
    {
        return byte_string{
            reinterpret_cast<unsigned char const *>(key.data()), key.size()};
    }

    void batch_erase_storage_for_address(
        statedb::KvStore &kv, rocksdb::WriteBatch &batch, Address const &addr,
        RocksDbCommitTrace *const trace = nullptr)
    {
        if (trace != nullptr) {
            ++trace->prefix_clears;
        }
        auto it = kv.new_iterator(Cf::flat_state);
        byte_string const start = storage_seek_key(addr);
        for (it->Seek(to_slice(start)); it->Valid(); it->Next()) {
            rocksdb::Slice const key = it->key();
            if (!is_storage_key_for_address(key, addr)) {
                break;
            }
            kv.batch_erase(batch, Cf::flat_state, to_byte_string(key));
            if (trace != nullptr) {
                ++trace->prefix_delete_keys;
            }
        }
        MONAD_ASSERT(it->status().ok());
    }

    bytes32_t to_bytes32(byte_string_view const b)
    {
        MONAD_ASSERT(b.size() == sizeof(bytes32_t));
        bytes32_t out{};
        std::memcpy(out.bytes, b.data(), sizeof(bytes32_t));
        return out;
    }

    // -----------------------------------------------------------------------
    // Witness collection (path-keyed). Walk CF_TRIE_NODES by trie PATH to each
    // touched key, appending the nodes on the path to the witness so
    // PartialTrieDb can re-materialize it. from_witness stays hash-indexed
    // internally; we just feed it the path-collected node RLPs. Child lookups
    // follow computed paths, not child-ref hashes. `may_delete` also pulls each
    // branch's hash-ref siblings into the witness for trie_delete's branch
    // compression. `key_prefix` is the bytes before the node-path nibbles:
    // {0x00} for the account trie, {0x01, account-path nibbles...} for a
    // storage trie (see node_key/account_node_key/storage_node_key below).
    // -----------------------------------------------------------------------

    using KeySet = std::set<byte_string>;

    void append_nibbles(byte_string &k, mpt::NibblesView const nv)
    {
        for (unsigned i = 0; i < nv.nibble_size(); ++i) {
            k.push_back(nv.get(i));
        }
    }

    byte_string
    node_key(byte_string_view const key_prefix, mpt::NibblesView const path)
    {
        byte_string k{key_prefix};
        append_nibbles(k, path);
        return k;
    }

    std::optional<byte_string> descend_payload(
        byte_string_view key_prefix, mpt::NibblesView node_path,
        byte_string_view payload, mpt::NibblesView remaining,
        statedb::TrieNodeStore &nodes, bool may_delete, KeySet &seen,
        byte_string &witness, RocksDbCommitTrace *trace);

    // Read the node at `node_path` (under key_prefix), append it to the witness
    // once, and descend toward `remaining`.
    std::optional<byte_string> descend(
        byte_string_view const key_prefix, mpt::NibblesView const node_path,
        mpt::NibblesView const remaining, statedb::TrieNodeStore &nodes,
        bool const may_delete, KeySet &seen, byte_string &witness,
        RocksDbCommitTrace *const trace)
    {
        byte_string const key = node_key(key_prefix, node_path);
        auto const node = nodes.get(key);
        if (trace != nullptr) {
            ++trace->node_gets;
            if (node.has_value()) {
                ++trace->node_hits;
            }
            else {
                ++trace->node_misses;
            }
        }
        if (!node.has_value()) {
            return std::nullopt; // path ends here (key is new/absent)
        }
        if (seen.insert(key).second) {
            witness.append(*node);
            if (trace != nullptr) {
                ++trace->witness_nodes;
                trace->witness_bytes += node->size();
            }
        }
        byte_string_view body{*node};
        auto const lm = rlp::parse_list_metadata(body);
        MONAD_ASSERT(!lm.has_error());
        return descend_payload(
            key_prefix,
            node_path,
            lm.value(),
            remaining,
            nodes,
            may_delete,
            seen,
            witness,
            trace);
    }

    void prefetch_node(
        byte_string_view const key_prefix, mpt::NibblesView const child_path,
        statedb::TrieNodeStore &nodes, KeySet &seen, byte_string &witness,
        RocksDbCommitTrace *const trace)
    {
        if (trace != nullptr) {
            ++trace->sibling_prefetches;
        }
        byte_string const key = node_key(key_prefix, child_path);
        if (!seen.insert(key).second) {
            return;
        }
        auto const node = nodes.get(key);
        if (trace != nullptr) {
            ++trace->node_gets;
            if (node.has_value()) {
                ++trace->node_hits;
            }
            else {
                ++trace->node_misses;
            }
        }
        if (node.has_value()) {
            witness.append(*node);
            if (trace != nullptr) {
                ++trace->witness_nodes;
                trace->witness_bytes += node->size();
            }
        }
    }

    std::optional<byte_string> descend_child(
        byte_string_view const key_prefix, mpt::NibblesView const child_path,
        rlp::RlpType const ty, byte_string_view const enc,
        mpt::NibblesView const remaining, statedb::TrieNodeStore &nodes,
        bool const may_delete, KeySet &seen, byte_string &witness,
        RocksDbCommitTrace *const trace)
    {
        if (ty == rlp::RlpType::List) {
            // Inline node: it lives in the parent's bytes (already in the
            // witness), so parse it in place -- no separate read/key.
            return descend_payload(
                key_prefix,
                child_path,
                enc,
                remaining,
                nodes,
                may_delete,
                seen,
                witness,
                trace);
        }
        if (enc.empty()) {
            return std::nullopt; // null child slot
        }
        // 32-byte hash ref: the child is stored at child_path; navigate by path
        // and ignore the ref hash.
        MONAD_ASSERT(enc.size() == 32);
        return descend(
            key_prefix,
            child_path,
            remaining,
            nodes,
            may_delete,
            seen,
            witness,
            trace);
    }

    // Mirrors decode_partial_node's structure detection. Returns the leaf /
    // branch value bytes if `remaining` resolves to one, else nullopt.
    std::optional<byte_string> descend_payload(
        byte_string_view const key_prefix, mpt::NibblesView const node_path,
        byte_string_view const payload, mpt::NibblesView const remaining,
        statedb::TrieNodeStore &nodes, bool const may_delete, KeySet &seen,
        byte_string &witness, RocksDbCommitTrace *const trace)
    {
        {
            byte_string_view short_enc{payload};
            auto const key_md = rlp::parse_metadata(short_enc);
            MONAD_ASSERT(!key_md.has_error());
            auto const val_md = rlp::parse_metadata(short_enc);
            MONAD_ASSERT(!val_md.has_error());
            if (short_enc.empty()) {
                // Extension or leaf (short node).
                MONAD_ASSERT(key_md.value().first == rlp::RlpType::String);
                auto const dec = mpt::compact_decode(key_md.value().second);
                MONAD_ASSERT(!dec.has_error());
                auto const &[decoded_path, is_leaf] = dec.value();
                mpt::NibblesView const pv{decoded_path};
                if (is_leaf) {
                    return (pv == remaining)
                               ? std::optional<byte_string>{byte_string{
                                     val_md.value().second}}
                               : std::nullopt;
                }
                if (!remaining.starts_with(pv)) {
                    return std::nullopt;
                }
                mpt::Nibbles const child_path = mpt::concat(node_path, pv);
                return descend_child(
                    key_prefix,
                    mpt::NibblesView{child_path},
                    val_md.value().first,
                    val_md.value().second,
                    remaining.substr(pv.nibble_size()),
                    nodes,
                    may_delete,
                    seen,
                    witness,
                    trace);
            }
        }

        // Branch node (17 items): re-parse from the start.
        byte_string_view enc{payload};
        std::array<std::pair<rlp::RlpType, byte_string_view>, 16> children;
        for (unsigned i = 0; i < 16; ++i) {
            auto const c = rlp::parse_metadata(enc);
            MONAD_ASSERT(!c.has_error());
            children[i] = c.value();
        }

        if (may_delete) {
            for (unsigned i = 0; i < 16; ++i) {
                if (children[i].first == rlp::RlpType::String &&
                    children[i].second.size() == 32) {
                    mpt::Nibbles const child_path =
                        mpt::concat(node_path, static_cast<unsigned char>(i));
                    prefetch_node(
                        key_prefix,
                        mpt::NibblesView{child_path},
                        nodes,
                        seen,
                        witness,
                        trace);
                }
            }
        }

        if (remaining.empty()) {
            auto const bv = rlp::decode_string(enc);
            MONAD_ASSERT(!bv.has_error());
            return bv.value().empty()
                       ? std::nullopt
                       : std::optional<byte_string>{byte_string{bv.value()}};
        }

        unsigned const nibble = remaining.get(0);
        mpt::Nibbles const child_path =
            mpt::concat(node_path, static_cast<unsigned char>(nibble));
        return descend_child(
            key_prefix,
            mpt::NibblesView{child_path},
            children[nibble].first,
            children[nibble].second,
            remaining.substr(1),
            nodes,
            may_delete,
            seen,
            witness,
            trace);
    }

    // CF_TRIE_NODES key prefixes (the bytes before the node-path nibbles).
    inline constexpr unsigned char ACCOUNT_TAG = 0x00;
    inline constexpr unsigned char STORAGE_TAG = 0x01;

    byte_string account_key_prefix()
    {
        return byte_string(1, ACCOUNT_TAG);
    }

    byte_string storage_key_prefix(mpt::NibblesView const account_path)
    {
        byte_string p(1, STORAGE_TAG);
        append_nibbles(p, account_path);
        return p;
    }
}

RocksDbDb::RocksDbDb(std::filesystem::path const &dir)
    : kv_{statedb::KvStore::open(dir)}
    // ~1M decoded nodes: the witness walk re-reads the trie's hot upper levels
    // every block, so keeping them in the LRU avoids repeated CF_TRIE_NODES
    // gets.
    , nodes_{*kv_, std::size_t{1} << 20}
{
    auto const sr = kv_->get(Cf::meta, meta_bsv(statedb::meta_key::state_root));
    state_root_ = sr.has_value() ? to_bytes32(*sr) : NULL_ROOT;

    auto const fb = kv_->get(Cf::meta, meta_bsv(statedb::meta_key::finalized));
    if (fb.has_value()) {
        block_number_ = decode_be64(*fb);
    }
    last_header_.number = block_number_;
}

RocksDbDb::~RocksDbDb() = default;

std::optional<Account> RocksDbDb::read_account(Address const &addr)
{
    auto const value = kv_->get(Cf::flat_state, account_key(addr));
    if (!value.has_value()) {
        return std::nullopt;
    }
    byte_string_view encoded{*value};
    return decode_account_db_ignore_address(encoded).value();
}

bytes32_t RocksDbDb::read_storage(
    Address const &addr, Incarnation const, bytes32_t const &slot)
{
    auto const value = kv_->get(Cf::flat_state, storage_key(addr, slot));
    if (!value.has_value()) {
        return {};
    }
    byte_string_view encoded{*value};
    auto const storage = decode_storage_db_ignore_key(encoded);
    MONAD_ASSERT(!storage.has_error());
    return to_bytes(storage.value());
}

vm::SharedIntercode RocksDbDb::read_code(bytes32_t const &code_hash)
{
    auto const value = kv_->get(
        Cf::code, byte_string_view{code_hash.bytes, sizeof(code_hash.bytes)});
    if (!value.has_value()) {
        return vm::make_shared_intercode({});
    }
    return vm::make_shared_intercode(
        std::span<uint8_t const>{value->data(), value->size()});
}

BlockHeader RocksDbDb::read_eth_header()
{
    return last_header_;
}

bytes32_t RocksDbDb::state_root()
{
    return state_root_;
}

bytes32_t RocksDbDb::receipts_root()
{
    return receipts_root_;
}

bytes32_t RocksDbDb::transactions_root()
{
    return transactions_root_;
}

std::optional<bytes32_t> RocksDbDb::withdrawals_root()
{
    return withdrawals_root_;
}

void RocksDbDb::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &)
{
    // Linear replay only: reads always observe the latest flat state, so the
    // block_id/proposal prefix is irrelevant in the prototype.
    block_number_ = block_number;
}

void RocksDbDb::finalize(uint64_t const block_number, bytes32_t const &)
{
    kv_->put(
        Cf::meta, meta_bsv(statedb::meta_key::finalized), be64(block_number));
    block_number_ = block_number;
}

void RocksDbDb::update_verified_block(uint64_t const block_number)
{
    kv_->put(
        Cf::meta, meta_bsv(statedb::meta_key::verified), be64(block_number));
}

void RocksDbDb::update_voted_metadata(uint64_t const, bytes32_t const &)
{
    // Consensus metadata: not needed for linear replay.
}

void RocksDbDb::update_proposed_metadata(uint64_t const, bytes32_t const &)
{
    // Consensus metadata: not needed for linear replay.
}

uint64_t RocksDbDb::get_block_number() const
{
    return block_number_;
}

bytes32_t RocksDbDb::apply_state_chunk(
    rocksdb::WriteBatch &batch, std::unique_ptr<StateDeltas> deltas,
    RocksDbCommitTrace *const trace)
{
    MONAD_ASSERT(deltas);

    // 1. Assemble a branch-complete witness for the touched keys by walking
    //    CF_TRIE_NODES by path. The account trie's root node sits at path key
    //    {ACCOUNT_TAG}; a storage trie's nodes at {STORAGE_TAG, account-path}.
    auto const witness_begin = Clock::now();
    byte_string witness;
    KeySet seen;
    mpt::Nibbles const root_path{}; // empty -> the trie root node
    if (state_root_ != NULL_ROOT) {
        byte_string const acct_prefix = account_key_prefix();
        for (auto const &[addr, delta] : *deltas) {
            auto const acct_hash = keccak256(addr.bytes);
            bool const acct_delete = !delta.account.second.has_value() &&
                                     delta.account.first.has_value();
            if (trace != nullptr) {
                ++trace->account_descends;
            }
            auto const leaf = descend(
                acct_prefix,
                mpt::NibblesView{root_path},
                mpt::NibblesView{acct_hash},
                nodes_,
                acct_delete,
                seen,
                witness,
                trace);

            if (!leaf.has_value() || !delta.account.second.has_value() ||
                delta.storage.empty()) {
                continue;
            }
            // Resolve the account's storage trie so touched slots are
            // materialized -- unless its incarnation changed this block, in
            // which case the old storage is wiped and rebuilt from the deltas.
            bool const inc_bump = delta.account.first.has_value() &&
                                  delta.account.first->incarnation !=
                                      delta.account.second->incarnation;
            if (inc_bump) {
                continue;
            }
            byte_string_view leaf_view{*leaf};
            bytes32_t storage_root{};
            auto const acct = rlp::decode_account(storage_root, leaf_view);
            MONAD_ASSERT(!acct.has_error());
            if (storage_root == NULL_ROOT) {
                continue;
            }
            byte_string const stor_prefix =
                storage_key_prefix(mpt::NibblesView{acct_hash});
            for (auto const &[slot, sdelta] : delta.storage) {
                bool const slot_delete =
                    sdelta.second == bytes32_t{} && sdelta.first != bytes32_t{};
                auto const slot_hash = keccak256(slot.bytes);
                if (trace != nullptr) {
                    ++trace->storage_descends;
                }
                descend(
                    stor_prefix,
                    mpt::NibblesView{root_path},
                    mpt::NibblesView{slot_hash},
                    nodes_,
                    slot_delete,
                    seen,
                    witness,
                    trace);
            }
        }
    }
    if (trace != nullptr) {
        trace->witness_us = elapsed_us(witness_begin);
        trace->witness_seen_keys = seen.size();
    }

    // 2. Re-materialize the touched trie and stage the flat writes.
    auto const from_witness_begin = Clock::now();
    auto pt = PartialTrieDb::from_witness(state_root_, witness, {});
    MONAD_ASSERT(!pt.has_error());
    if (trace != nullptr) {
        trace->from_witness_us = elapsed_us(from_witness_begin);
    }

    auto const flat_begin = Clock::now();
    for (auto const &[addr, delta] : *deltas) {
        if (trace != nullptr) {
            ++trace->accounts;
        }
        auto const &new_acct = delta.account.second;
        bool const account_deleted =
            !new_acct.has_value() && delta.account.first.has_value();
        bool const inc_bump =
            new_acct.has_value() && delta.account.first.has_value() &&
            delta.account.first->incarnation != new_acct->incarnation;

        if (new_acct.has_value()) {
            if (trace != nullptr) {
                ++trace->account_puts;
            }
            kv_->batch_put(
                batch,
                Cf::flat_state,
                account_key(addr),
                encode_account_db(addr, *new_acct));
        }
        else if (delta.account.first.has_value()) {
            if (trace != nullptr) {
                ++trace->account_deletes;
            }
            kv_->batch_erase(batch, Cf::flat_state, account_key(addr));
        }
        if (account_deleted || inc_bump) {
            if (trace != nullptr && inc_bump) {
                ++trace->incarnation_bumps;
            }
            batch_erase_storage_for_address(*kv_, batch, addr, trace);
        }
        if (!new_acct.has_value()) {
            continue;
        }
        for (auto const &[slot, sdelta] : delta.storage) {
            if (trace != nullptr) {
                ++trace->storage_deltas;
            }
            byte_string const sk = storage_key(addr, slot);
            if (sdelta.second == bytes32_t{}) {
                if (trace != nullptr) {
                    ++trace->storage_deletes;
                }
                kv_->batch_erase(batch, Cf::flat_state, sk);
            }
            else {
                if (trace != nullptr) {
                    ++trace->storage_puts;
                }
                kv_->batch_put(
                    batch,
                    Cf::flat_state,
                    sk,
                    encode_storage_db(slot, sdelta.second));
            }
        }
    }
    if (trace != nullptr) {
        trace->flat_stage_us = elapsed_us(flat_begin);
    }

    // 3. Apply the deltas to the witness trie, recompute the root, and stage
    // the
    //    changed trie nodes. PartialTrieDb ignores block_id/builder/header.
    CommitBuilder unused{0};
    auto const trie_replay_begin = Clock::now();
    pt.value().commit(
        bytes32_t{},
        unused,
        BlockHeader{},
        std::move(deltas),
        [](BlockHeader &) {});
    bytes32_t const root = pt.value().state_root();
    if (trace != nullptr) {
        trace->trie_replay_us = elapsed_us(trie_replay_begin);
    }
    auto const trie_stage_begin = Clock::now();
    pt.value().for_each_node(
        [&](mpt::NibblesView const path,
            std::optional<mpt::NibblesView> const storage_account,
            byte_string_view const rlp) {
            byte_string key = storage_account.has_value()
                                  ? storage_key_prefix(*storage_account)
                                  : account_key_prefix();
            append_nibbles(key, path);
            if (trace != nullptr) {
                ++trace->trie_node_puts;
                trace->trie_node_put_bytes +=
                    statedb::TRIE_NODE_HEADER_SIZE + rlp.size();
            }
            nodes_.batch_put(batch, key, rlp);
        });
    if (trace != nullptr) {
        trace->trie_stage_us = elapsed_us(trie_stage_begin);
    }
    return root;
}

void RocksDbDb::seed_chunk(
    std::unique_ptr<StateDeltas> deltas, Code const &code)
{
    MONAD_ASSERT(deltas);
    rocksdb::WriteBatch batch;
    for (auto const &[code_hash, icode] : code) {
        if (icode) {
            auto const span = icode->code_span();
            kv_->batch_put(
                batch,
                Cf::code,
                byte_string_view{code_hash.bytes, sizeof(code_hash.bytes)},
                byte_string_view{span.data(), span.size()});
        }
    }
    state_root_ = apply_state_chunk(batch, std::move(deltas));
    // Per-chunk durability is not needed: a crashed seed is simply re-run.
    kv_->write(batch, /*sync=*/false);
}

void RocksDbDb::seed_finalize(
    uint64_t const block, bytes32_t const &expected_state_root)
{
    // The seed gate: the folded state must reproduce the snapshot's root.
    MONAD_ASSERT(state_root_ == expected_state_root);
    rocksdb::WriteBatch batch;
    kv_->batch_put(
        batch,
        Cf::meta,
        meta_bsv(statedb::meta_key::state_root),
        byte_string_view{state_root_.bytes, sizeof(state_root_.bytes)});
    kv_->batch_put(
        batch, Cf::meta, meta_bsv(statedb::meta_key::finalized), be64(block));
    kv_->write(batch, /*sync=*/true);
    block_number_ = block;
}

void RocksDbDb::commit(
    bytes32_t const &, CommitBuilder &builder, BlockHeader const &header,
    std::unique_ptr<StateDeltas> state_deltas,
    std::function<void(BlockHeader &)> const populate_header_fn)
{
    MONAD_ASSERT(state_deltas);

    RocksDbCommitTrace trace;
    trace.block = header.number;
    auto const total_begin = Clock::now();

    rocksdb::WriteBatch batch;

    // 3. Recompute the block-local roots (receipts/transactions/withdrawals)
    //    and recover any new contract code -- both live only in the
    //    CommitBuilder. Build the block's update tree, drop the incremental
    //    *state* section (its deletions have no prior key in a fresh trie; the
    //    remaining sections are wipe-or-insert-only), and upsert the rest into
    //    a throwaway in-memory trie. State stays block-sized; the real state
    //    root comes from the on-disk trie in step 4.
    auto const build_begin = Clock::now();
    mpt::UpdateList built = builder.build(mpt::NibblesView{finalized_nibbles});
    MONAD_ASSERT(!built.empty());
    {
        mpt::UpdateList &sections = built.front().next;
        for (auto it = sections.begin(); it != sections.end();) {
            if (it->key == mpt::NibblesView{state_nibbles}) {
                it = sections.erase(it);
            }
            else {
                ++it;
            }
        }
    }
    trace.build_us = elapsed_us(build_begin);

    auto const local_roots_begin = Clock::now();
    mpt::Db inmem{std::make_unique<InMemoryMachine>()};
    auto const inmem_root = inmem.upsert(
        mpt::Node::SharedPtr{},
        std::move(built),
        header.number,
        true,
        true,
        false);

    auto const sub_root = [&](mpt::Nibbles const &section) -> bytes32_t {
        auto const r = inmem.find(
            inmem_root,
            mpt::concat(
                mpt::NibblesView{finalized_nibbles}, mpt::NibblesView{section}),
            header.number);
        if (!r.has_value() || r.value().node->data().empty()) {
            return NULL_ROOT;
        }
        return to_bytes(r.value().node->data());
    };
    receipts_root_ = sub_root(receipt_nibbles);
    transactions_root_ = sub_root(transaction_nibbles);
    {
        auto const r = inmem.find(
            inmem_root,
            mpt::concat(mpt::NibblesView{finalized_nibbles}, WITHDRAWAL_NIBBLE),
            header.number);
        if (!r.has_value()) {
            withdrawals_root_ = std::nullopt;
        }
        else {
            withdrawals_root_ = r.value().node->data().empty()
                                    ? NULL_ROOT
                                    : to_bytes(r.value().node->data());
        }
    }
    trace.local_roots_us = elapsed_us(local_roots_begin);

    auto const code_stage_begin = Clock::now();
    for (auto const &[addr, delta] : *state_deltas) {
        if (!delta.account.second.has_value()) {
            continue;
        }
        ++trace.code_candidates;
        bytes32_t const &code_hash = delta.account.second->code_hash;
        auto const r = inmem.find(
            inmem_root,
            mpt::concat(
                mpt::NibblesView{finalized_nibbles},
                CODE_NIBBLE,
                mpt::NibblesView{to_byte_string_view(code_hash.bytes)}),
            header.number);
        if (r.has_value() && !r.value().node->value().empty()) {
            ++trace.code_puts;
            trace.code_put_bytes += r.value().node->value().size();
            kv_->batch_put(
                batch,
                Cf::code,
                byte_string_view{code_hash.bytes, sizeof(code_hash.bytes)},
                r.value().node->value());
        }
    }
    trace.code_stage_us = elapsed_us(code_stage_begin);

    // 4. Fold the state deltas into the on-disk trie + flat CFs, staging the
    //    changed nodes/values into the same batch, and take the new root.
    auto const state_chunk_begin = Clock::now();
    state_root_ = apply_state_chunk(batch, std::move(state_deltas), &trace);
    trace.state_chunk_us = elapsed_us(state_chunk_begin);

    // 5. Fill the output header via the caller's callback (it reads the roots
    //    back through this object's getters, now holding the post-commit
    //    values), then stage CF_META.
    BlockHeader complete_header = header;
    MONAD_ASSERT(populate_header_fn);
    auto const populate_header_begin = Clock::now();
    populate_header_fn(complete_header);
    trace.populate_header_us = elapsed_us(populate_header_begin);
    last_header_ = complete_header;
    block_number_ = header.number;

    auto const meta_stage_begin = Clock::now();
    kv_->batch_put(
        batch,
        Cf::meta,
        meta_bsv(statedb::meta_key::state_root),
        byte_string_view{state_root_.bytes, sizeof(state_root_.bytes)});
    kv_->batch_put(
        batch,
        Cf::meta,
        meta_bsv(statedb::meta_key::finalized),
        be64(header.number));
    trace.meta_stage_us = elapsed_us(meta_stage_begin);
    trace.batch_keys = batch.Count();
    trace.batch_bytes = batch.GetDataSize();

    // 6. Single WriteBatch: flat + code + trie nodes + meta, atomic across CFs.
    //    Async WAL (no per-block fsync) -- a crashed replay is simply re-run
    //    from the seed, and the in-memory roots/validation are unaffected. The
    //    bounded async write-back queue is the fuller F10 treatment.
    auto const write_begin = Clock::now();
    kv_->write(batch, /*sync=*/false);
    trace.write_us = elapsed_us(write_begin);
    trace.total_us = elapsed_us(total_begin);
    log_commit_trace(trace);
}

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
