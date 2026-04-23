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
#include <category/core/nibble.h>
#include <category/mpt/compute.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/traverse_util.hpp>
#include <category/mpt/update.hpp>

#include <cassert>
#include <filesystem>
#include <iostream>
#include <memory>
#include <system_error>
#include <utility>
#include <vector>

namespace monad::rust
{
    namespace
    {
        void nibbles_to_bytes(
            uint8_t *dest, monad::mpt::NibblesView const nibbles,
            size_t const nibble_count)
        {
            for (unsigned n = 0; n < static_cast<unsigned>(nibble_count); ++n) {
                set_nibble(dest, n, nibbles.get(n));
            }
        }

        monad::mpt::NibblesView
        to_view(::rust::Slice<uint8_t const> key, uint8_t const key_len_nibbles)
        {
            return monad::mpt::NibblesView{
                0u, static_cast<unsigned>(key_len_nibbles), key.data()};
        }

        // Minimal StateMachine for RW opens: no compute, always compact.
        class PlainStateMachine final : public monad::mpt::StateMachine
        {
        public:
            std::unique_ptr<monad::mpt::StateMachine> clone() const override
            {
                return std::make_unique<PlainStateMachine>(*this);
            }

            void down(unsigned char) override {}

            void up(size_t) override {}

            monad::mpt::Compute &get_compute() const override
            {
                static monad::mpt::EmptyCompute e{};
                return e;
            }

            bool cache() const override
            {
                return true;
            }

            bool compact() const override
            {
                return true;
            }

            bool is_variable_length() const override
            {
                return false;
            }
        };
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
            std::cerr << "Failed to inspect database path: " << path << " ("
                      << ec.message() << ")\n";
            return nullptr;
        }

        try {
            return std::make_unique<TriedbRoInner>(
                monad::mpt::ReadOnlyOnDiskDbConfig{
                    .disable_mismatching_storage_pool_check =
                        disable_mismatching_storage_pool_check,
                    .dbname_paths = std::move(paths)},
                node_lru_max_mem);
        }
        catch (std::exception const &e) {
            std::cerr << e.what() << '\n';
            return nullptr;
        }
    }

    namespace
    {
        std::unique_ptr<TriedbRwInner>
        open_rw_impl(monad::mpt::OnDiskDbConfig config)
        {
            try {
                return std::make_unique<TriedbRwInner>(
                    std::make_unique<PlainStateMachine>(), config);
            }
            catch (std::exception const &e) {
                std::cerr << e.what() << '\n';
                return nullptr;
            }
        }
    }

    std::unique_ptr<TriedbRwInner> triedb_open_rw_memory(
        uint64_t const /*node_lru_max_mem*/, int64_t const file_size_gb,
        bool const compaction)
    {
        // Empty dbname_paths triggers use_anonymous_sized_inode_tag in
        // AsyncIOContext(OnDiskDbConfig).
        return open_rw_impl(monad::mpt::OnDiskDbConfig{
            .append = false,
            .compaction = compaction,
            .dbname_paths = {},
            .file_size_db = file_size_gb});
    }

    std::unique_ptr<TriedbRwInner> triedb_open_rw(
        ::rust::Str dbdirpath, bool const append,
        uint64_t const /*node_lru_max_mem*/, int64_t const file_size_gb,
        bool const compaction)
    {
        std::string const path{dbdirpath.data(), dbdirpath.size()};
        std::vector<std::filesystem::path> paths;
        paths.emplace_back(path);
        return open_rw_impl(monad::mpt::OnDiskDbConfig{
            .append = append,
            .compaction = compaction,
            .dbname_paths = std::move(paths),
            .file_size_db = file_size_gb});
    }

    ::rust::Slice<uint8_t const>
    node_cursor_value(monad::mpt::NodeCursor const &cursor)
    {
        auto const &value = cursor.node->value();
        return {value.data(), value.size()};
    }

    namespace
    {
        struct AsyncReadReceiver
        {
            Context *ctx;

            void set_value(
                monad::async::erased_connected_operation *state,
                monad::async::result<monad::byte_string> result)
            {
                if (!result) {
                    ::rust::Slice<uint8_t const> empty{};
                    async_read_on_complete(ctx, empty, false);
                }
                else {
                    auto const &value = result.value();
                    ::rust::Slice<uint8_t const> view{
                        value.data(), value.size()};
                    async_read_on_complete(ctx, view, true);
                }
                delete state;
            }
        };
    }

    void triedb_async_read(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> const key,
        uint8_t const key_len_nibbles, uint64_t const block_id,
        Context *const ctx)
    {
        auto *state = new auto(monad::async::connect(
            monad::mpt::make_get_sender(
                &inner.async_ctx, to_view(key, key_len_nibbles), block_id),
            AsyncReadReceiver{ctx}));
        state->initiate();
    }

    namespace
    {
        class CallbackTraverse final : public monad::mpt::TraverseMachine
        {
        public:
            CallbackTraverse(
                Context *const ctx, monad::mpt::NibblesView initial)
                : ctx_(ctx)
                , path_(initial)
            {
            }

            bool down(unsigned char const branch, monad::mpt::Node const &node)
                override
            {
                if (branch == monad::mpt::INVALID_BRANCH) {
                    return true;
                }
                path_ = monad::mpt::concat(
                    monad::mpt::NibblesView{path_},
                    branch,
                    node.path_nibble_view());

                if (node.has_value()) {
                    assert((path_.nibble_size() & 1) == 0);
                    size_t const path_bytes = path_.nibble_size() / 2;
                    auto path_data = std::make_unique<uint8_t[]>(path_bytes);
                    nibbles_to_bytes(
                        path_data.get(), path_, path_.nibble_size());

                    auto const &value = node.value();
                    ::rust::Slice<uint8_t const> key_slice{
                        path_data.get(), path_bytes};
                    ::rust::Slice<uint8_t const> value_slice{
                        value.data(), value.size()};
                    traverse_value_callback(ctx_, key_slice, value_slice);
                    return false;
                }
                return true;
            }

            void
            up(unsigned char const branch,
               monad::mpt::Node const &node) override
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

            std::unique_ptr<TraverseMachine> clone() const override
            {
                return std::make_unique<CallbackTraverse>(*this);
            }

        private:
            Context *ctx_;
            monad::mpt::Nibbles path_;
        };

        struct TraverseFinishedReceiver
        {
            Context *ctx;

            void set_value(
                monad::async::erased_connected_operation *state,
                monad::async::result<bool> res)
            {
                MONAD_ASSERT_PRINTF(
                    res,
                    "triedb_async_traverse: Traversing failed with %s",
                    res.assume_error().message().c_str());
                traverse_finished_callback(ctx, res.assume_value());
                delete state;
            }
        };

        struct TraverseRootReceiver
        {
            using ResultType =
                monad::async::result<std::shared_ptr<monad::mpt::Node>>;

            monad::mpt::detail::TraverseSender traverse_sender;
            Context *ctx;

            TraverseRootReceiver(
                monad::mpt::detail::TraverseSender sender, Context *const ctx)
                : traverse_sender(std::move(sender))
                , ctx(ctx)
            {
            }

            void set_value(
                monad::async::erased_connected_operation *state, ResultType res)
            {
                if (!res) {
                    traverse_finished_callback(ctx, false);
                }
                else {
                    traverse_sender.traverse_root = res.assume_value();
                    auto *next = new auto(monad::async::connect(
                        std::move(traverse_sender),
                        TraverseFinishedReceiver{ctx}));
                    next->initiate();
                }
                delete state;
            }
        };
    }

    bool triedb_traverse_sync(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> const key,
        uint8_t const key_len_nibbles, uint64_t const block_id,
        Context *const ctx)
    {
        auto cursor = inner.db.find(to_view(key, key_len_nibbles), block_id);
        if (!cursor.has_value()) {
            return false;
        }
        CallbackTraverse machine(ctx, monad::mpt::NibblesView{});
        return inner.db.traverse(cursor.value(), machine, block_id);
    }

    void triedb_async_traverse(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> const key,
        uint8_t const key_len_nibbles, uint64_t const block_id,
        Context *const ctx)
    {
        auto const prefix = to_view(key, key_len_nibbles);
        auto machine =
            std::make_unique<CallbackTraverse>(ctx, monad::mpt::NibblesView{});
        auto *state = new auto(monad::async::connect(
            monad::mpt::make_get_node_sender(
                &inner.async_ctx, prefix, block_id),
            TraverseRootReceiver{
                monad::mpt::make_traverse_sender(
                    &inner.async_ctx, {}, std::move(machine), block_id),
                ctx}));
        state->initiate();
    }

    void triedb_async_ranged_get(
        TriedbRoInner &inner, ::rust::Slice<uint8_t const> const prefix_key,
        uint8_t const prefix_key_len_nibbles,
        ::rust::Slice<uint8_t const> const min_key,
        uint8_t const min_key_len_nibbles,
        ::rust::Slice<uint8_t const> const max_key,
        uint8_t const max_key_len_nibbles, uint64_t const block_id,
        Context *const user)
    {
        auto const prefix = to_view(prefix_key, prefix_key_len_nibbles);
        auto const min = to_view(min_key, min_key_len_nibbles);
        auto const max = to_view(max_key, max_key_len_nibbles);

        auto machine = std::make_unique<monad::mpt::RangedGetMachine>(
            min,
            max,
            [user](
                monad::mpt::NibblesView const k,
                monad::byte_string_view const v) {
                size_t const key_len_nibbles = k.nibble_size();
                assert((key_len_nibbles & 1) == 0);
                size_t const key_len_bytes = key_len_nibbles / 2;
                auto key_data = std::make_unique<uint8_t[]>(key_len_bytes);
                nibbles_to_bytes(key_data.get(), k, key_len_nibbles);

                ::rust::Slice<uint8_t const> key_slice{
                    key_data.get(), key_len_bytes};
                ::rust::Slice<uint8_t const> value_slice{v.data(), v.size()};
                traverse_value_callback(user, key_slice, value_slice);
            });

        auto *state = new auto(monad::async::connect(
            monad::mpt::make_get_node_sender(
                &inner.async_ctx, prefix, block_id),
            TraverseRootReceiver{
                monad::mpt::make_traverse_sender(
                    &inner.async_ctx, {}, std::move(machine), block_id),
                user}));
        state->initiate();
    }

    ::rust::Vec<monad::staking::Validator> triedb_read_valset(
        TriedbRoInner &inner, size_t const block_num,
        uint64_t const requested_epoch, bool &found)
    {
        ::rust::Vec<monad::staking::Validator> out;
        auto ret =
            monad::staking::read_valset(inner.db, block_num, requested_epoch);
        if (!ret.has_value()) {
            found = false;
            return out;
        }
        found = true;
        auto const &valset = ret.value();
        out.reserve(valset.size());
        for (auto const &v : valset) {
            out.push_back(v);
        }
        return out;
    }

    void triedb_upsert(
        TriedbRwInner &inner, ::rust::Slice<UpsertEntry const> const updates,
        uint64_t const block_id)
    {
        // UpdateList is intrusive, so Update instances must outlive the list.
        std::vector<monad::mpt::Update> update_storage;
        update_storage.reserve(updates.size());

        monad::mpt::UpdateList update_list;
        for (auto const &entry : updates) {
            update_storage.push_back(monad::mpt::make_update(
                to_view(
                    ::rust::Slice<uint8_t const>{
                        entry.key.data(), entry.key.size()},
                    entry.key_nibble_len),
                monad::byte_string_view{
                    entry.value.data(), entry.value.size()}));
            update_list.push_front(update_storage.back());
        }

        inner.root = inner.db.upsert(
            std::move(inner.root), std::move(update_list), block_id);
    }

    void triedb_clear_root(TriedbRwInner &inner)
    {
        inner.root.reset();
    }

    bool triedb_load_root(TriedbRwInner &inner, uint64_t const version)
    {
        auto root = inner.db.load_root_for_version(version);
        if (root == nullptr) {
            return false;
        }
        inner.root = std::move(root);
        return true;
    }

    void triedb_update_finalized_version(
        TriedbRwInner &inner, uint64_t const version)
    {
        inner.db.update_finalized_version(version);
    }

    void triedb_update_voted_metadata(
        TriedbRwInner &inner, uint64_t const version,
        monad::bytes32_t const &block_id)
    {
        inner.db.update_voted_metadata(version, block_id);
    }

    void triedb_update_proposed_metadata(
        TriedbRwInner &inner, uint64_t const version,
        monad::bytes32_t const &block_id)
    {
        inner.db.update_proposed_metadata(version, block_id);
    }
}
