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

    #include <ankerl/unordered_dense.h>

    #include <rocksdb/write_batch.h>

    #include <array>
    #include <cstdint>
    #include <cstring>
    #include <memory>
    #include <optional>
    #include <utility>

MONAD_NAMESPACE_BEGIN

using statedb::Cf;

namespace
{
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

    bytes32_t to_bytes32(byte_string_view const b)
    {
        MONAD_ASSERT(b.size() == sizeof(bytes32_t));
        bytes32_t out{};
        std::memcpy(out.bytes, b.data(), sizeof(bytes32_t));
        return out;
    }

    // -----------------------------------------------------------------------
    // Witness collection: walk CF_TRIE_NODES along the path to a key, adding
    // every node on the path to the witness so PartialTrieDb can re-materialize
    // it. Absent subtrees become HashStubs in from_witness (their hash is
    // preserved by the parent's child-ref), which is all the root recompute
    // needs. `may_delete` additionally pulls every immediate hash-ref child of
    // each branch on the path into the witness, so trie_delete's branch
    // compression can reach the sole surviving sibling (which must not be a
    // stub).
    // -----------------------------------------------------------------------

    using HashSet = ankerl::unordered_dense::set<bytes32_t>;

    std::optional<byte_string> descend_payload(
        byte_string_view payload, mpt::NibblesView remaining,
        statedb::TrieNodeStore &nodes, bool may_delete, HashSet &seen,
        byte_string &witness);

    void prefetch_node(
        bytes32_t const &h, statedb::TrieNodeStore &nodes, HashSet &seen,
        byte_string &witness)
    {
        if (h == NULL_ROOT || !seen.insert(h).second) {
            return;
        }
        auto const node = nodes.get(h);
        MONAD_ASSERT(node.has_value());
        witness.append(*node);
    }

    std::optional<byte_string> descend_hash(
        bytes32_t const &h, mpt::NibblesView remaining,
        statedb::TrieNodeStore &nodes, bool may_delete, HashSet &seen,
        byte_string &witness)
    {
        if (h == NULL_ROOT) {
            return std::nullopt;
        }
        auto const node = nodes.get(h);
        MONAD_ASSERT(node.has_value()); // any node on a real path must exist
        if (seen.insert(h).second) {
            witness.append(*node);
        }
        byte_string_view body{*node};
        auto const lm = rlp::parse_list_metadata(body);
        MONAD_ASSERT(!lm.has_error());
        return descend_payload(
            lm.value(), remaining, nodes, may_delete, seen, witness);
    }

    std::optional<byte_string> descend_child(
        rlp::RlpType const ty, byte_string_view enc, mpt::NibblesView remaining,
        statedb::TrieNodeStore &nodes, bool may_delete, HashSet &seen,
        byte_string &witness)
    {
        if (ty == rlp::RlpType::List) {
            // Inline (embedded) node: `enc` is its list payload already.
            return descend_payload(
                enc, remaining, nodes, may_delete, seen, witness);
        }
        if (enc.empty()) {
            return std::nullopt; // null child slot
        }
        MONAD_ASSERT(enc.size() == 32);
        return descend_hash(
            to_bytes32(enc), remaining, nodes, may_delete, seen, witness);
    }

    // Mirrors decode_partial_node's structure detection. Returns the leaf /
    // branch value bytes if `remaining` resolves to one, else nullopt.
    std::optional<byte_string> descend_payload(
        byte_string_view const payload, mpt::NibblesView remaining,
        statedb::TrieNodeStore &nodes, bool const may_delete, HashSet &seen,
        byte_string &witness)
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
                auto const &[path, is_leaf] = dec.value();
                mpt::NibblesView const pv{path};
                if (is_leaf) {
                    return (pv == remaining)
                               ? std::optional<byte_string>{byte_string{
                                     val_md.value().second}}
                               : std::nullopt;
                }
                if (!remaining.starts_with(pv)) {
                    return std::nullopt;
                }
                return descend_child(
                    val_md.value().first,
                    val_md.value().second,
                    remaining.substr(pv.nibble_size()),
                    nodes,
                    may_delete,
                    seen,
                    witness);
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
            for (auto const &[ty, child_enc] : children) {
                if (ty == rlp::RlpType::String && child_enc.size() == 32) {
                    prefetch_node(to_bytes32(child_enc), nodes, seen, witness);
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
        return descend_child(
            children[nibble].first,
            children[nibble].second,
            remaining.substr(1),
            nodes,
            may_delete,
            seen,
            witness);
    }
}

RocksDbDb::RocksDbDb(std::filesystem::path const &dir)
    : kv_{statedb::KvStore::open(dir)}
    , nodes_{*kv_, std::size_t{1} << 16}
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
    Address const &addr, Incarnation const incarnation, bytes32_t const &slot)
{
    auto const value =
        kv_->get(Cf::flat_state, storage_key(addr, incarnation, slot));
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

void RocksDbDb::commit(
    bytes32_t const &block_id, CommitBuilder &builder,
    BlockHeader const &header, std::unique_ptr<StateDeltas> state_deltas,
    std::function<void(BlockHeader &)> const populate_header_fn)
{
    MONAD_ASSERT(state_deltas);

    // 1. Assemble a branch-complete witness for the touched keys.
    byte_string witness;
    HashSet seen;
    if (state_root_ != NULL_ROOT) {
        for (auto const &[addr, delta] : *state_deltas) {
            auto const acct_hash = keccak256(addr.bytes);
            bool const acct_delete = !delta.account.second.has_value() &&
                                     delta.account.first.has_value();
            auto const leaf = descend_hash(
                state_root_,
                mpt::NibblesView{acct_hash},
                nodes_,
                acct_delete,
                seen,
                witness);

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
            for (auto const &[slot, sdelta] : delta.storage) {
                bool const slot_delete =
                    sdelta.second == bytes32_t{} && sdelta.first != bytes32_t{};
                auto const slot_hash = keccak256(slot.bytes);
                descend_hash(
                    storage_root,
                    mpt::NibblesView{slot_hash},
                    nodes_,
                    slot_delete,
                    seen,
                    witness);
            }
        }
    }

    // 2. Re-materialize the touched trie and stage the flat writes.
    auto pt = PartialTrieDb::from_witness(state_root_, witness, {});
    MONAD_ASSERT(!pt.has_error());

    rocksdb::WriteBatch batch;
    for (auto const &[addr, delta] : *state_deltas) {
        auto const &new_acct = delta.account.second;
        if (new_acct.has_value()) {
            kv_->batch_put(
                batch,
                Cf::flat_state,
                account_key(addr),
                encode_account_db(addr, *new_acct));
        }
        else if (delta.account.first.has_value()) {
            kv_->batch_erase(batch, Cf::flat_state, account_key(addr));
        }
        Incarnation const incarnation =
            new_acct.has_value() ? new_acct->incarnation
                                 : (delta.account.first.has_value()
                                        ? delta.account.first->incarnation
                                        : Incarnation{0, 0});
        for (auto const &[slot, sdelta] : delta.storage) {
            byte_string const sk = storage_key(addr, incarnation, slot);
            if (sdelta.second == bytes32_t{}) {
                kv_->batch_erase(batch, Cf::flat_state, sk);
            }
            else {
                kv_->batch_put(
                    batch,
                    Cf::flat_state,
                    sk,
                    encode_storage_db(slot, sdelta.second));
            }
        }
    }

    // 3. Recompute the block-local roots (receipts/transactions/withdrawals)
    //    and recover any new contract code -- both live only in the
    //    CommitBuilder. Build the block's update tree, drop the incremental
    //    *state* section (its deletions have no prior key in a fresh trie; the
    //    remaining sections are wipe-or-insert-only), and upsert the rest into
    //    a throwaway in-memory trie. State stays block-sized; the real state
    //    root comes from the on-disk trie in step 4.
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

    for (auto const &[addr, delta] : *state_deltas) {
        if (!delta.account.second.has_value()) {
            continue;
        }
        bytes32_t const &code_hash = delta.account.second->code_hash;
        auto const r = inmem.find(
            inmem_root,
            mpt::concat(
                mpt::NibblesView{finalized_nibbles},
                CODE_NIBBLE,
                mpt::NibblesView{to_byte_string_view(code_hash.bytes)}),
            header.number);
        if (r.has_value() && !r.value().node->value().empty()) {
            kv_->batch_put(
                batch,
                Cf::code,
                byte_string_view{code_hash.bytes, sizeof(code_hash.bytes)},
                r.value().node->value());
        }
    }

    // 4. Apply the state deltas to the witness trie, recompute the root, and
    //    stage the changed trie nodes. PartialTrieDb ignores block_id/builder.
    CommitBuilder unused{header.number};
    pt.value().commit(
        block_id, unused, header, std::move(state_deltas), [](BlockHeader &) {
        });
    state_root_ = pt.value().state_root();
    pt.value().for_each_node(
        [&](bytes32_t const &node_hash, byte_string_view const rlp) {
            nodes_.batch_put(batch, node_hash, rlp);
        });

    // 5. Fill the output header via the caller's callback (it reads the roots
    //    back through this object's getters, now holding the post-commit
    //    values), then stage CF_META.
    BlockHeader complete_header = header;
    MONAD_ASSERT(populate_header_fn);
    populate_header_fn(complete_header);
    last_header_ = complete_header;
    block_number_ = header.number;

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

    // 6. Single synchronous WriteBatch: flat + code + trie nodes + meta, atomic
    //    across CFs with a WAL fsync.
    kv_->write(batch, /*sync=*/true);
}

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
