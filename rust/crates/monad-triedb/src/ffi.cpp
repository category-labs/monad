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

#include "monad-triedb/include/ffi.h"
#include "monad-triedb/src/ffi.rs.h"

#include <category/async/connected_operation.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/log.hpp>
#include <category/core/nibble.h>
#include <category/mpt/compute.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/traverse_util.hpp>

#include <cassert>
#include <filesystem>
#include <memory>
#include <system_error>
#include <utility>
#include <vector>

namespace monad::rust
{

    TriedbRoInner::TriedbRoInner(
        std::vector<std::filesystem::path> dbname_paths,
        uint64_t const node_lru_max_mem,
        bool const disable_mismatching_storage_pool_check)
        : io_ctx(monad::mpt::ReadOnlyOnDiskDbConfig{
              .disable_mismatching_storage_pool_check =
                  disable_mismatching_storage_pool_check,
              .dbname_paths = std::move(dbname_paths)})
        , db(io_ctx)
        , async_ctx(db, node_lru_max_mem)
    {
    }

    void nibbles_to_bytes(
        uint8_t *dest, monad::mpt::NibblesView const nibbles,
        size_t const nibble_count)
    {
        for (unsigned n = 0; n < static_cast<unsigned>(nibble_count); ++n) {
            set_nibble(dest, n, nibbles.get(n));
        }
    }

    monad::mpt::NibblesView to_mpt_view(NibblesView const &view)
    {
        unsigned nibble_count = static_cast<unsigned>(view.bytes.size() * 2);

        if (nibble_count > 0 && view.odd) {
            nibble_count -= 1;
        }

        return monad::mpt::NibblesView{0u, nibble_count, view.bytes.data()};
    }

    std::unique_ptr<TriedbRoInner> triedb_open(
        ::rust::Str dbdirpath, uint64_t const node_lru_max_mem,
        bool const disable_mismatching_storage_pool_check)
    {
        std::string const path{dbdirpath.data(), dbdirpath.size()};

        std::vector<std::filesystem::path> paths;
        std::error_code ec;

        if (std::filesystem::is_block_file(path, ec)) {
            paths.emplace_back(path);
        }
        else if (!ec) {
            for (auto const &file :
                 std::filesystem::directory_iterator(path, ec)) {
                paths.emplace_back(file.path());
            }
        }

        if (ec) {
            LOG_ERROR("Failed to inspect database path: {} ({})", path, ec);
            return nullptr;
        }

        try {
            return std::make_unique<TriedbRoInner>(
                std::move(paths),
                node_lru_max_mem,
                disable_mismatching_storage_pool_check);
        }
        catch (std::exception const &e) {
            LOG_ERROR("Failed to open triedb: {}", e.what());
            return nullptr;
        }
    }

    std::unique_ptr<monad::mpt::NodeCursor>
    triedb_read(TriedbRoInner const &inner, NibblesView key, uint64_t block_id)
    {
        auto result = inner.db.find(to_mpt_view(key), block_id);
        if (!result.has_value()) {
            return nullptr;
        }
        return std::make_unique<monad::mpt::NodeCursor>(
            std::move(result.value()));
    }

    struct AsyncReadReceiver
    {
        ffi::CallbackContext *ctx;

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<monad::byte_string> result)
        {
            if (!result) {
                ::rust::Slice<uint8_t const> empty{};
                ffi::callback_async_read(ctx, empty, false);
            }
            else {
                monad::byte_string const &value = result.value();
                ::rust::Slice<uint8_t const> view{value.data(), value.size()};
                ffi::callback_async_read(ctx, view, true);
            }
            delete state;
        }
    };

    void triedb_async_read(
        TriedbRoInner &inner, NibblesView const key, uint64_t const block_id,
        ffi::CallbackContext *const ctx)
    {
        auto *state = new auto(monad::async::connect(
            monad::mpt::make_get_sender(
                &inner.async_ctx, to_mpt_view(key), block_id),
            AsyncReadReceiver{ctx}));
        state->initiate();
    }

    class TraverseMachineWithCallback final : public monad::mpt::TraverseMachine
    {
    private:
        ffi::CallbackContext *ctx_;
        monad::mpt::Nibbles path_;

    public:
        TraverseMachineWithCallback(
            ffi::CallbackContext *const ctx,
            monad::mpt::NibblesView const initial_path)
            : ctx_(ctx)
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
                auto const &value = node.value();
                ::rust::Slice<uint8_t const> key_slice{
                    path_data.get(), path_bytes};
                ::rust::Slice<uint8_t const> value_slice{
                    value.data(), value.size()};
                ffi::callback_traverse_value(ctx_, key_slice, value_slice);
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
            return std::make_unique<TraverseMachineWithCallback>(*this);
        }
    };

    struct TraverseReceiver
    {
        ffi::CallbackContext *ctx;

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<bool> res)
        {
            MONAD_ASSERT_PRINTF(
                res,
                "triedb_async_traverse: Traversing failed with %s",
                res.assume_error().message().c_str());
            ffi::callback_traverse_finished(ctx, res.assume_value());
            delete state;
        }
    };

    struct GetRootForTraverseReceiver
    {
        ffi::CallbackContext *ctx;
        monad::mpt::detail::TraverseSender traverse_sender;

        GetRootForTraverseReceiver(
            ffi::CallbackContext *const ctx,
            monad::mpt::detail::TraverseSender traverse_sender_)
            : ctx(ctx)
            , traverse_sender(std::move(traverse_sender_))
        {
        }

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<std::shared_ptr<monad::mpt::Node>> res)
        {
            if (!res) {
                ffi::callback_traverse_finished(ctx, false);
            }
            else {
                traverse_sender.traverse_root = res.assume_value();
                (new auto(monad::async::connect(
                     std::move(traverse_sender), TraverseReceiver{ctx})))
                    ->initiate();
            }
            delete state;
        }
    };

    void triedb_traverse(
        TriedbRoInner &inner, NibblesView const key, uint64_t const block_id,
        ffi::CallbackContext *const ctx)
    {
        auto cursor = inner.db.find(to_mpt_view(key), block_id);

        if (!cursor.has_value()) {
            ffi::callback_traverse_finished(ctx, false);
            return;
        }

        TraverseMachineWithCallback machine(ctx, monad::mpt::NibblesView{});

        bool const completed =
            inner.db.traverse(cursor.value(), machine, block_id);

        ffi::callback_traverse_finished(ctx, completed);
    }

    void triedb_async_ranged_get(
        TriedbRoInner &inner, NibblesView const prefix_view,
        NibblesView const min_view, NibblesView const max_view,
        uint64_t const block_id, ffi::CallbackContext *const ctx)
    {
        monad::mpt::NibblesView const prefix = to_mpt_view(prefix_view);
        monad::mpt::NibblesView const min = to_mpt_view(min_view);
        monad::mpt::NibblesView const max = to_mpt_view(max_view);

        auto machine = std::make_unique<monad::mpt::RangedGetMachine>(
            min,
            max,
            [ctx](
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

                ::rust::Slice<uint8_t const> key_slice{
                    key_data.get(), key_len_bytes};
                ::rust::Slice<uint8_t const> value_slice{
                    value.data(), value.size()};

                ffi::callback_traverse_value(ctx, key_slice, value_slice);
            });

        (new auto(monad::async::connect(
             monad::mpt::make_get_node_sender(
                 &inner.async_ctx, prefix, block_id),
             GetRootForTraverseReceiver{
                 ctx,
                 monad::mpt::make_traverse_sender(
                     &inner.async_ctx, {}, std::move(machine), block_id),
             })))
            ->initiate();
    }

    void triedb_async_traverse(
        TriedbRoInner &inner, NibblesView const key, uint64_t const block_id,
        ffi::CallbackContext *const ctx)
    {
        monad::mpt::NibblesView const prefix = to_mpt_view(key);

        auto machine = std::make_unique<TraverseMachineWithCallback>(
            ctx, monad::mpt::NibblesView{});

        (new auto(monad::async::connect(
             monad::mpt::make_get_node_sender(
                 &inner.async_ctx, prefix, block_id),
             GetRootForTraverseReceiver{
                 ctx,
                 monad::mpt::make_traverse_sender(
                     &inner.async_ctx, {}, std::move(machine), block_id),
             })))
            ->initiate();
    }

    std::unique_ptr<std::vector<monad::staking::Validator>> triedb_read_valset(
        TriedbRoInner &db, size_t const block_num,
        uint64_t const requested_epoch)
    {
        auto ret =
            monad::staking::read_valset(db.db, block_num, requested_epoch);
        if (!ret.has_value()) {
            return nullptr;
        }
        return std::make_unique<std::vector<monad::staking::Validator>>(
            std::move(ret).value());
    }

} // namespace monad::rust
