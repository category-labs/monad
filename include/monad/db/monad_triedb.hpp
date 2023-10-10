#pragma once

#include <monad/db/config.hpp>
#include <monad/db/db.hpp>

#include <monad/core/keccak.h>
#include <monad/rlp/decode_helpers.hpp>

#include <monad/mpt/compute.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

MONAD_DB_NAMESPACE_BEGIN

struct ComputeLeafData
{
    static byte_string compute(mpt::Node const *const node)
    {
        if (node->n() == 0) { // can be either account or storage
            return byte_string{node->leaf_view()};
        }
        // rlp decode node->leaf_view() to Account,
        // encode Account with storage hash to the computed leaf
        Account acc;
        bytes32_t storage_root;
        rlp::decode_account(acc, storage_root, node->leaf_view());
        std::memcpy(storage_root.bytes, node->hash_data(), node->hash_len);
        return rlp::encode_account(acc, storage_root);
    }
};

using MyMerkleCompute = mpt::details::MerkleComputeBase<ComputeLeafData>;

// TEMPORARY: in-memory triedb for now
struct MonadTrieDB final : Db
{
    virtual std::optional<Account>
    read_account(address_t const &a) const override
    {
        unsigned char hash_addr[32];
        keccak256(a.bytes, sizeof(a.bytes), hash_addr);

        mpt::Node *node =
            mpt::find(root.get(), byte_string_view{hash_addr, 32});
        if (!node) {
            return std::nullopt;
        }
        Account ret;
        bytes32_t _;
        auto const rest = rlp::decode_account(ret, _, node->leaf_view());
        MONAD_ASSERT(rest.empty());
        return ret;
    }

    virtual bytes32_t
    read_storage(address_t const &a, bytes32_t const &key) const override
    {
        unsigned char hash_addr[32], hash_key[32];
        keccak256(a.bytes, sizeof(a.bytes), hash_addr);
        keccak256(key.bytes, sizeof(key.bytes), hash_key);
        // find account
        mpt::Node *acc_leaf =
            mpt::find(root.get(), byte_string_view{hash_addr, 32});
        if (!acc_leaf) {
            return bytes32_t{};
        }
        mpt::Node *storage_leaf = mpt::find(
            acc_leaf,
            byte_string_view{hash_key, 32},
            acc_leaf->path_nibble_index_end);
        if (!storage_leaf) {
            return bytes32_t{};
        }
        // decode storage leaf data
        byte_string zeroless;
        auto const rest =
            rlp::decode_string(zeroless, storage_leaf->leaf_view());
        MONAD_ASSERT(rest.empty());
        MONAD_ASSERT(zeroless.size() <= sizeof(bytes32_t));

        bytes32_t ret;
        std::copy_n(
            zeroless.data(),
            zeroless.size(),
            std::next(
                std::begin(ret.bytes),
                static_cast<uint8_t>(sizeof(bytes32_t) - zeroless.size())));
        MONAD_ASSERT(ret != bytes32_t{});
        return ret;
    }

    virtual byte_string read_code(bytes32_t const &ch) const override
    {
        if (code.contains(ch)) {
            return code.at(ch);
        }
        return byte_string{};
    }

    virtual void
    commit(StateDeltas const &state_deltas, Code const &code_delta) override
    {
        for (auto const &[ch, c] : code_delta) {
            code[ch] = c;
        }
        // convert state delta to nested list
        std::vector<mpt::Update> account_update_vec;
        std::vector<std::vector<mpt::Update>> storage_update_vec;
        std::vector<byte_string> hashed_keys; // addr and storage keys
        std::vector<byte_string> values;
        values.reserve(100); // TEMPORARY solution to avoid byte_string being
                             // moved around in memory
        std::vector<mpt::UpdateList> storage_updatelists;
        storage_updatelists.reserve(state_deltas.size());

        for (auto const &[addr, state_delta] : state_deltas) {
            auto const &account_delta = state_delta.account;
            auto const &storage_delta = state_delta.storage;

            mpt::UpdateList storage_updates;
            std::vector<mpt::Update> tmp_vec;
            if (account_delta.second.has_value()) {
                // only add storage updates if not account deletion
                for (auto const &[k, v] : storage_delta) {
                    if (v.first != v.second) {
                        hashed_keys.emplace_back(32, 0);
                        auto &key = hashed_keys.back();
                        keccak256(
                            k.bytes,
                            sizeof(k.bytes),
                            const_cast<unsigned char *>(key.data()));

                        if (v.second != bytes32_t{}) {
                            auto const value = rlp::encode_string(zeroless_view(
                                to_byte_string_view(v.second.bytes)));
                            values.push_back(std::move(value));
                            tmp_vec.emplace_back(
                                mpt::make_update(key, values.back()));
                        }
                        else {
                            tmp_vec.emplace_back(mpt::make_erase(key));
                        }
                        // storage_updates.push_front(account_update_vec.back());
                    }
                }
                for (auto &update : tmp_vec) {
                    storage_updates.push_front(update);
                }
                storage_update_vec.push_back(std::move(tmp_vec));
            }
            // add an account update if anything changed
            // storage_updates can be empty
            mpt::UpdateList *nested_list = nullptr;
            if (!storage_updates.empty()) {
                storage_updatelists.push_back(std::move(storage_updates));
                nested_list = &storage_updatelists.back();
                assert(nested_list != nullptr);
            }

            if (account_delta.first != account_delta.second ||
                nested_list != nullptr) {
                hashed_keys.emplace_back(32, 0);
                auto &key = hashed_keys.back();
                keccak256(
                    addr.bytes,
                    sizeof(addr.bytes),
                    const_cast<unsigned char *>(key.data()));

                if (account_delta.second.has_value()) {
                    // value is bytes of account
                    auto const value = rlp::encode_account(
                        account_delta.second.value(), NULL_ROOT);
                    values.push_back(std::move(value));
                    account_update_vec.emplace_back(mpt::make_update(
                        key,
                        values.back(),
                        /*incarnation*/ false,
                        nested_list));
                }
                else {
                    account_update_vec.emplace_back(mpt::make_erase(key));
                }
            }
        }

        mpt::UpdateList state_updates;
        for (auto &update : account_update_vec) {
            state_updates.push_front(update);
        }
        if (!state_updates.empty()) {
            root =
                mpt::upsert(update_aux, root.get(), std::move(state_updates));
        }
    }

    virtual void
    create_and_prune_block_history(uint64_t /*block number*/) const override
    {
    }

    [[nodiscard]] bytes32_t state_root()
    {
        if (!root) {
            return NULL_ROOT;
        }
        bytes32_t ret;
        comp.compute(ret.bytes, root.get());
        return ret;
    }

    [[nodiscard]] bytes32_t storage_root(address_t const &a)
    {
        unsigned char hash_addr[32];
        keccak256(a.bytes, sizeof(a.bytes), hash_addr);

        mpt::Node *node = mpt::find(root.get(), byte_string_view{hash_addr});
        bytes32_t res;
        MONAD_ASSERT(node->hash_len == 32);
        std::memcpy(res.bytes, node->hash_data(), node->hash_len);
        return res;
    }

private:
    mpt::node_ptr root{};
    MyMerkleCompute comp{};
    mpt::UpdateAux update_aux{comp};
    std::unordered_map<bytes32_t, byte_string> code;
};

MONAD_DB_NAMESPACE_END
