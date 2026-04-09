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

#include <cassert>
#include <filesystem>
#include <iostream>
#include <limits>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

#include <category/core/byte_string.hpp>
#include <category/core/nibble.h>
#include <category/execution/monad/staking/read_valset.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/traverse_util.hpp>

#include "triedb.h"

// Convert a nibble path into a packed byte array.
void nibbles_to_bytes(
    uint8_t *dest, monad::mpt::NibblesView const nibbles,
    size_t const nibble_count)
{
    for (unsigned n = 0; n < static_cast<unsigned>(nibble_count); ++n) {
        set_nibble(dest, n, nibbles.get(n));
    }
}

struct triedb
{
    explicit triedb(
        std::vector<std::filesystem::path> dbname_paths,
        uint64_t const node_lru_max_mem)
        : io_ctx_{monad::mpt::ReadOnlyOnDiskDbConfig{
              .disable_mismatching_storage_pool_check = true,
              .dbname_paths = std::move(dbname_paths)}}
        , db_{io_ctx_}
        , ctx_{monad::mpt::async_context_create(db_, node_lru_max_mem)}
    {
    }

    monad::mpt::AsyncIOContext io_ctx_;
    monad::mpt::Db db_;
    monad::mpt::AsyncContextUniquePtr ctx_;
};

int triedb_open(
    char const *dbdirpath, triedb **db, uint64_t const node_lru_max_mem)
{
    if (dbdirpath == nullptr || db == nullptr || *db != nullptr) {
        return -1;
    }

    std::vector<std::filesystem::path> paths;
    std::error_code ec;

    if (std::filesystem::is_block_file(dbdirpath, ec)) {
        paths.emplace_back(dbdirpath);
    }
    else if (!ec) {
        for (auto const &file :
             std::filesystem::directory_iterator(dbdirpath, ec)) {
            paths.emplace_back(file.path());
        }
    }

    if (ec) {
        return -2;
    }

    try {
        *db = new triedb{std::move(paths), node_lru_max_mem};
    }
    catch (std::exception const &e) {
        std::cerr << e.what();
        return -3;
    }
    return 0;
}

int triedb_close(triedb *db)
{
    delete db;
    return 0;
}

int triedb_read(
    triedb *db, uint8_t const *const key, uint8_t const key_len_nibbles,
    uint8_t const **value, uint64_t const block_id)
{
    if (db == nullptr || value == nullptr) {
        return -3;
    }

    *value = nullptr;

    auto result = db->db_.find(
        monad::mpt::NibblesView{0, key_len_nibbles, key}, block_id);
    if (!result.has_value()) {
        return -1;
    }

    auto const &value_view = result.value().node->value();
    if (value_view.size() >
        static_cast<size_t>(std::numeric_limits<int>::max())) {
        // value length doesn't fit in return type
        return -2;
    }
    int const value_len = static_cast<int>(value_view.size());
    if (value_len > 0) {
        uint8_t *buf = new uint8_t[value_len];
        memcpy(buf, value_view.data(), value_len);
        *value = buf;
    }
    return value_len;
}

void triedb_async_read(
    triedb *db, uint8_t const *const key, uint8_t const key_len_nibbles,
    uint64_t const block_id,
    void (*completed)(uint8_t const *value, int length, void *user), void *user)
{
    struct receiver_t
    {
        void (*completed_)(uint8_t const *value, int length, void *user);
        void *user_;

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<monad::byte_string> result)
        {
            uint8_t const *value = nullptr;
            int length = 0;
            auto const completed = completed_;
            void *const user = user_;
            if (!result) {
                length = -1;
            }
            else {
                auto const &value_view = result.value();
                if (value_view.size() >
                    static_cast<size_t>(std::numeric_limits<int>::max())) {
                    // value length doesn't fit in return type
                    length = -2;
                }
                else {
                    length = static_cast<int>(value_view.size());
                    if (length > 0) {
                        uint8_t *buf = new uint8_t[length];
                        memcpy(
                            buf,
                            value_view.data(),
                            static_cast<size_t>(length));
                        value = buf;
                    }
                }
            }
            delete state;
            completed(value, length, user);
        }
    };

    auto *state = new auto(monad::async::connect(
        monad::mpt::make_get_sender(
            db->ctx_.get(),
            monad::mpt::NibblesView{0, key_len_nibbles, key},
            block_id),
        receiver_t{completed, user}));
    state->initiate();
}

namespace detail
{
    class Traverse final : public monad::mpt::TraverseMachine
    {
        void *context_;
        triedb_async_traverse_callback_fn callback_;
        monad::mpt::Nibbles path_;

    public:
        Traverse(
            void *context, triedb_async_traverse_callback_fn callback,
            monad::mpt::NibblesView const initial_path)
            : context_(context)
            , callback_(callback)
            , path_(initial_path)
        {
        }

        virtual bool
        down(unsigned char const branch, monad::mpt::Node const &node) override
        {
            if (branch == monad::mpt::INVALID_BRANCH) {
                return true;
            }
            path_ = monad::mpt::concat(
                monad::mpt::NibblesView{path_},
                branch,
                node.path_nibble_view());

            if (node.has_value()) { // node is a leaf
                assert(
                    (path_.nibble_size() & 1) == 0); // assert even nibble size
                size_t const path_bytes = path_.nibble_size() / 2;
                auto path_data = std::make_unique<uint8_t[]>(path_bytes);

                nibbles_to_bytes(path_data.get(), path_, path_.nibble_size());

                // path_data is key, node.value().data() is rlp(value)
                callback_(
                    triedb_async_traverse_callback_value,
                    context_,
                    path_data.get(),
                    path_bytes,
                    node.value().data(),
                    node.value().size());

                return false;
            }

            return true;
        }

        virtual void
        up(unsigned char const branch, monad::mpt::Node const &node) override
        {
            monad::mpt::NibblesView const path_view{path_};
            int const rem_size = [&] {
                if (branch == monad::mpt::INVALID_BRANCH) {
                    return 0;
                }
                return path_view.nibble_size() - 1 -
                       node.path_nibble_view().nibble_size();
            }();
            path_ = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }
    };

    struct TraverseReceiver
    {
        void *context;
        triedb_async_traverse_callback_fn callback;

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<bool> res)
        {
            MONAD_ASSERT_PRINTF(
                res,
                "triedb_async_traverse: Traversing failed with %s",
                res.assume_error().message().c_str());
            callback(
                res.assume_value()
                    ? triedb_async_traverse_callback_finished_normally
                    : triedb_async_traverse_callback_finished_early,
                context,
                nullptr,
                0,
                nullptr,
                0);
            delete state; // deletes this
        }
    };

    struct GetNodeReceiver
    {
        using ResultType =
            monad::async::result<std::shared_ptr<monad::mpt::Node>>;

        monad::mpt::detail::TraverseSender traverse_sender;
        TraverseReceiver traverse_receiver;

        GetNodeReceiver(
            void *context, triedb_async_traverse_callback_fn callback,
            monad::mpt::detail::TraverseSender traverse_sender_)
            : traverse_sender(std::move(traverse_sender_))
            , traverse_receiver(context, callback)
        {
        }

        void set_value(
            monad::async::erased_connected_operation *state, ResultType res)
        {
            if (!res) {
                traverse_receiver.callback(
                    triedb_async_traverse_callback_finished_early,
                    traverse_receiver.context,
                    nullptr,
                    0,
                    nullptr,
                    0);
            }
            else {
                traverse_sender.traverse_root = res.assume_value();
                (new auto(monad::async::connect(
                     std::move(traverse_sender), std::move(traverse_receiver))))
                    ->initiate();
            }
            delete state; // deletes this
        }
    };
}

bool triedb_traverse(
    triedb *db, uint8_t const *const key, uint8_t const key_len_nibbles,
    uint64_t const block_id, void *context,
    triedb_async_traverse_callback_fn callback)
{
    monad::mpt::NibblesView const prefix{0, key_len_nibbles, key};
    auto cursor = db->db_.find(prefix, block_id);
    if (!cursor.has_value()) {
        callback(
            triedb_async_traverse_callback_finished_early,
            context,
            nullptr,
            0,
            nullptr,
            0);
        return false;
    }

    detail::Traverse machine(context, callback, monad::mpt::NibblesView{});

    bool const completed = db->db_.traverse(cursor.value(), machine, block_id);

    callback(
        completed ? triedb_async_traverse_callback_finished_normally
                  : triedb_async_traverse_callback_finished_early,
        context,
        nullptr,
        0,
        nullptr,
        0);
    return completed;
}

void triedb_async_ranged_get(
    triedb *db, uint8_t const *const prefix_key,
    uint8_t const prefix_len_nibbles, uint8_t const *const min_key,
    uint8_t const min_len_nibbles, uint8_t const *const max_key,
    uint8_t const max_len_nibbles, uint64_t const block_id, void *context,
    triedb_async_traverse_callback_fn callback)
{
    monad::mpt::NibblesView const prefix{0, prefix_len_nibbles, prefix_key};
    monad::mpt::NibblesView const min{0, min_len_nibbles, min_key};
    monad::mpt::NibblesView const max{0, max_len_nibbles, max_key};
    auto machine = std::make_unique<monad::mpt::RangedGetMachine>(
        min,
        max,
        [callback, context](
            monad::mpt::NibblesView const key,
            monad::byte_string_view const value) {
            size_t const key_len_nibbles = key.nibble_size();
            MONAD_ASSERT_PRINTF(
                (key_len_nibbles & 1) == 0,
                "Only supported for even length paths but got %lu nibbles",
                key_len_nibbles);
            size_t const key_len_bytes = key_len_nibbles / 2;
            auto key_data = std::make_unique<uint8_t[]>(key_len_bytes);

            nibbles_to_bytes(key_data.get(), key, key_len_nibbles);

            callback(
                triedb_async_traverse_callback_value,
                context,
                key_data.get(),
                key_len_bytes,
                value.data(),
                value.size());
        });
    (new auto(monad::async::connect(
         monad::mpt::make_get_node_sender(db->ctx_.get(), prefix, block_id),
         detail::GetNodeReceiver(
             context,
             callback,
             monad::mpt::make_traverse_sender(
                 db->ctx_.get(), {}, std::move(machine), block_id)))))
        ->initiate();
}

void triedb_async_traverse(
    triedb *db, uint8_t const *const key, uint8_t const key_len_nibbles,
    uint64_t const block_id, void *context,
    triedb_async_traverse_callback_fn callback)
{
    monad::mpt::NibblesView const prefix{0, key_len_nibbles, key};
    auto machine = std::make_unique<detail::Traverse>(
        context, callback, monad::mpt::NibblesView{});
    (new auto(monad::async::connect(
         monad::mpt::make_get_node_sender(db->ctx_.get(), prefix, block_id),
         detail::GetNodeReceiver(
             context,
             callback,
             monad::mpt::make_traverse_sender(
                 db->ctx_.get(), {}, std::move(machine), block_id)))))
        ->initiate();
}

size_t triedb_poll(triedb *db, bool const blocking, size_t const count)
{
    return db->db_.poll(blocking, count);
}

int triedb_finalize(uint8_t const *const value)
{
    delete[] value;
    return 0;
}

uint64_t triedb_latest_proposed_block(triedb *db)
{
    return db->db_.get_latest_proposed_version();
}

monad_c_bytes32 triedb_latest_proposed_block_id(triedb *db)
{
    return db->db_.get_latest_proposed_block_id();
}

uint64_t triedb_latest_voted_block(triedb *db)
{
    return db->db_.get_latest_voted_version();
}

monad_c_bytes32 triedb_latest_voted_block_id(triedb *db)
{
    return db->db_.get_latest_voted_block_id();
}

uint64_t triedb_latest_finalized_block(triedb *db)
{
    return db->db_.get_latest_finalized_version();
}

uint64_t triedb_latest_verified_block(triedb *db)
{
    return db->db_.get_latest_verified_version();
}

uint64_t triedb_earliest_finalized_block(triedb *db)
{
    return db->db_.get_earliest_version();
}

validator_set *alloc_valset(uint64_t const length)
{
    validator_data *validators = new validator_data[length];
    return new validator_set{.validators = validators, .length = length};
}

void triedb_free_valset(validator_set *valset)
{
    delete[] valset->validators;
    delete valset;
}

validator_set *triedb_read_valset(
    triedb *db, size_t const block_num, uint64_t const requested_epoch)
{
    auto ret = monad::staking::read_valset(db->db_, block_num, requested_epoch);
    if (!ret.has_value()) {
        return nullptr;
    }

    uint64_t const length = ret.value().size();
    validator_set *valset = alloc_valset(length);
    for (uint64_t i = 0; i < length; ++i) {
        std::memcpy(
            valset->validators[i].secp_pubkey, ret.value()[i].secp_pubkey, 33);
        std::memcpy(
            valset->validators[i].bls_pubkey, ret.value()[i].bls_pubkey, 48);
        std::memcpy(
            valset->validators[i].stake, ret.value()[i].stake.bytes, 32);
    }

    return valset;
}
