#include <cassert>
#include <filesystem>
#include <iostream>
#include <limits>
#include <memory>
#include <optional>
#include <vector>

#include <monad/core/byte_string.hpp>
#include <monad/core/nibble.h>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/traverse_util.hpp>

#include "triedb.h"

struct triedb
{
    explicit triedb(std::vector<std::filesystem::path> dbname_paths)
        : io_ctx_{monad::mpt::ReadOnlyOnDiskDbConfig{
              .disable_mismatching_storage_pool_check = true,
              .dbname_paths = std::move(dbname_paths)}}
        , db_{io_ctx_}
        , ctx_{monad::mpt::async_context_create(db_)}
    {
    }

    monad::mpt::AsyncIOContext io_ctx_;
    monad::mpt::Db db_;
    monad::mpt::AsyncContextUniquePtr ctx_;
};

int triedb_open(char const *dbdirpath, triedb **db)
{
    if (*db != nullptr) {
        return -1;
    }

    std::vector<std::filesystem::path> paths;
    if (std::filesystem::is_block_file(dbdirpath) ||
        std::filesystem::is_regular_file(dbdirpath)) {
        paths.emplace_back(dbdirpath);
    }
    else {
        std::error_code ec;
        for (auto const &file :
             std::filesystem::directory_iterator(dbdirpath, ec)) {
            paths.emplace_back(file.path());
        }
        if (ec) {
            return -2;
        }
    }

    try {
        *db = new triedb{std::move(paths)};
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
    triedb *db, bytes key, uint8_t key_len_nibbles, bytes *value,
    uint64_t block_id)
{
    auto result =
        db->db_.get(monad::mpt::NibblesView{0, key_len_nibbles, key}, block_id);
    if (!result.has_value()) {
        return -1;
    }

    auto const &value_view = result.value();
    if ((value_view.size() >> std::numeric_limits<int>::digits) != 0) {
        // value length doesn't fit in return type
        return -2;
    }
    size_t const value_len = value_view.size();
    *value = new uint8_t[value_len];
    memcpy((void *)*value, value_view.data(), value_len);
    return (int)value_len;
}

void triedb_async_read(
    triedb *db, bytes key, uint8_t key_len_nibbles, uint64_t block_id,
    void (*completed)(bytes value, int length, void *user), void *user)
{
    struct receiver_t
    {
        void (*completed_)(bytes value, int length, void *user);
        void *user_;

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<monad::byte_string> result)
        {
            bytes value = nullptr;
            int length = 0;
            auto completed = completed_;
            auto user = user_;
            if (!result) {
                length = -1;
            }
            else {
                auto const &value_view = result.value();
                if ((value_view.size() >> std::numeric_limits<int>::digits) !=
                    0) {
                    // value length doesn't fit in return type
                    length = -2;
                }
                else {
                    length = (int)value_view.size();
                    value = new uint8_t[(size_t)length];
                    memcpy((void *)value, value_view.data(), (size_t)length);
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
        callback_func callback_;
        monad::mpt::Nibbles path_;

    public:
        Traverse(
            void *context, callback_func callback,
            monad::mpt::NibblesView initial_path)
            : context_(std::move(context))
            , callback_(std::move(callback))
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
                size_t path_bytes = path_.nibble_size() / 2;
                auto path_data = std::make_unique<uint8_t[]>(path_bytes);

                for (unsigned n = 0; n < (unsigned)path_.nibble_size(); ++n) {
                    set_nibble(path_data.get(), n, path_.get(n));
                }

                // path_data is key, node.value().data() is
                // rlp(value)
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
            auto const path_view = monad::mpt::NibblesView{path_};
            auto const rem_size = [&] {
                if (branch == monad::mpt::INVALID_BRANCH) {
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                return rem_size;
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
        callback_func callback;

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
        monad::mpt::detail::TraverseSender traverse_sender;
        TraverseReceiver traverse_receiver;

        GetNodeReceiver(
            void *context, callback_func callback,
            monad::mpt::detail::TraverseSender traverse_sender_)
            : traverse_sender(std::move(traverse_sender_))
            , traverse_receiver(context, callback)
        {
        }

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<monad::mpt::Node::UniquePtr> res)
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
                traverse_sender.traverse_root = std::move(res).assume_value();
                (new auto(monad::async::connect(
                     std::move(traverse_sender), std::move(traverse_receiver))))
                    ->initiate();
            }
            delete state; // deletes this
        }
    };
}

bool triedb_traverse(
    triedb *db, bytes key, uint8_t key_len_nibbles, uint64_t block_id,
    void *context, callback_func callback)
{
    auto prefix = monad::mpt::NibblesView{0, key_len_nibbles, key};
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
    triedb *db, bytes prefix_key, uint8_t prefix_len_nibbles, bytes min_key,
    uint8_t min_len_nibbles, bytes max_key, uint8_t max_len_nibbles,
    uint64_t block_id, void *context, callback_func callback)
{
    monad::mpt::NibblesView const prefix{0, prefix_len_nibbles, prefix_key};
    monad::mpt::NibblesView const min{0, min_len_nibbles, min_key};
    monad::mpt::NibblesView const max{0, max_len_nibbles, max_key};
    auto machine = std::make_unique<monad::mpt::RangedGetMachine>(
        min,
        max,
        [callback, context](
            monad::mpt::NibblesView const key, monad::byte_string_view value) {
            size_t key_len_nibbles = key.nibble_size();
            MONAD_ASSERT_PRINTF(
                (key_len_nibbles & 1) == 0,
                "Only supported for even length paths but got %lu nibbles",
                key_len_nibbles);
            size_t key_len_bytes = key_len_nibbles / 2;
            auto key_data = std::make_unique<uint8_t[]>(key_len_bytes);

            for (unsigned n = 0; n < (unsigned)key_len_nibbles; ++n) {
                set_nibble(key_data.get(), n, key.get(n));
            }
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
    triedb *db, bytes key, uint8_t key_len_nibbles, uint64_t block_id,
    void *context, callback_func callback)
{
    auto prefix = monad::mpt::NibblesView{0, key_len_nibbles, key};
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

size_t triedb_poll(triedb *db, bool blocking, size_t count)
{
    return db->db_.poll(blocking, count);
}

int triedb_finalize(bytes value)
{
    delete[] value;
    return 0;
}

uint64_t triedb_latest_voted_block(triedb *db)
{
    uint64_t latest_voted_block_id = db->db_.get_latest_voted_block_id();
    return latest_voted_block_id;
}

uint64_t triedb_latest_voted_round(triedb *db)
{
    uint64_t latest_round = db->db_.get_latest_voted_round();
    return latest_round;
}

uint64_t triedb_latest_finalized_block(triedb *db)
{
    uint64_t latest_block_id = db->db_.get_latest_finalized_block_id();
    return latest_block_id;
}

uint64_t triedb_latest_verified_block(triedb *db)
{
    uint64_t latest_block_id = db->db_.get_latest_verified_block_id();
    return latest_block_id;
}

uint64_t triedb_earliest_finalized_block(triedb *db)
{
    uint64_t earliest_block_id = db->db_.get_earliest_block_id();
    return earliest_block_id;
}
