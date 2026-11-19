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

#pragma once

#include <category/async/config.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/util.hpp>

#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <thread>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

class UpdateAux;

namespace detail
{
    struct list_bytes
    {
        uint64_t fast{0};
        uint64_t slow{0};

        bool operator==(list_bytes const &) const = default;
    };

    struct space_delta
    {
        list_bytes written; // bytes of counted nodes written into each list
        list_bytes superseded; // bytes of nodes that stopped being live
        // False when a dropped subtrie could not be read, so `superseded`
        // misses its bytes.
        bool complete{true};

        void add(space_delta const &) noexcept;
    };

    // Per list: max(0, live + written - superseded).
    list_bytes apply(list_bytes live, space_delta const &) noexcept;

    // Sums collected per proposal from commit to finalize. Only the
    // finalized proposal's sums reach the counters: a losing proposal's
    // supersedes replaced nodes that stay live in the winning chain, and its
    // writes are garbage.
    class settlement_table
    {
        struct entry
        {
            uint64_t version;
            space_delta delta;
        };

        std::map<bytes32_t, entry> entries_;

    public:
        void add(bytes32_t const &key, uint64_t version, space_delta const &);

        // The winner's sums, nullopt if it has no entry; every entry at or
        // below `version` is erased, the winner's included.
        std::optional<space_delta>
        settle(uint64_t version, bytes32_t const &winner);

        void discard(bytes32_t const &key);

        size_t size() const noexcept;
    };

    // Live-byte accounting of an on-disk UpdateAux.
    struct space_accounting
    {
        // A node whose children stopped being live along with it. `machine`
        // is positioned at the node, or null where everything below counts.
        struct dropped_node
        {
            Node::SharedPtr node;
            std::unique_ptr<StateMachine> machine;
        };

        // Touched only by the upserting thread.
        space_delta upsert_delta;
        std::optional<bytes32_t> settlement_key;
        // The unkeyed upsert changes only a root older than the counted one.
        bool older_root{false};
        bool count_writes{true};
        std::optional<uint32_t> slow_collection_override; // 64 KiB units
        std::vector<dropped_node> dropped; // read at the end of the upsert

        mutable std::mutex mutex; // guards the members below
        settlement_table table;
        std::optional<list_bytes> live; // nullopt while unknown
        // Newest version whose changes `live` includes; the persisted stamp.
        uint64_t live_version{INVALID_BLOCK_NUM};
        // `live` includes an unkeyed upsert whose root is not published, so
        // it must not be persisted until a restamp.
        bool root_pending{false};

        // Background walk that fills unknown counters.
        Nibbles prefix; // where the walk starts; empty: the whole root
        // Positioned at the root; null until the first upsert supplies it.
        std::unique_ptr<StateMachine> machine;
        bool walk_running{false};
        bool walk_done{false};
        bool walk_gave_up{false};
        unsigned walk_attempts{0};
        uint64_t walk_version{INVALID_BLOCK_NUM};
        std::chrono::steady_clock::time_point walk_started;
        std::optional<list_bytes> walk_result;
        space_delta since_walk; // applied after the walk's version
        uint64_t since_walk_version{INVALID_BLOCK_NUM};
        std::atomic<bool> walk_paused{false};
        std::jthread walk_thread; // last member: joins before the rest goes
    };

    // Bytes of every counted node strictly below `node`, per list, read on
    // the calling thread. `machine` is positioned at `node` and decides which
    // subtries count (StateMachine::counts_live_bytes_below); null counts
    // every node. nullopt if `version` stops being valid, or a chunk below
    // has been freed.
    std::optional<list_bytes> bytes_below(
        UpdateAux &, Node const &node, uint64_t version, timeline_id,
        StateMachine const *machine);

    // bytes_below() of the node that `prefix` reaches from `root` (`root`
    // itself for an empty prefix), with `machine` positioned at `root`,
    // split across threads that each run an async traversal with their own
    // read-only i/o. A node reached by two paths is counted twice, so the
    // result is exact only where the subtrie is a tree; copy_trie shares
    // subtries between prefixes, so a pool that uses it must be walked below
    // one prefix. `keep_going` is asked from those threads before every
    // node; false abandons the walk with nullopt.
    std::optional<list_bytes> walk_live_bytes(
        UpdateAux const &, MONAD_ASYNC_NAMESPACE::chunk_offset_t root,
        uint64_t version, timeline_id, NibblesView prefix = {},
        StateMachine const *machine = nullptr,
        std::function<bool()> const &keep_going = {});
}

MONAD_MPT_NAMESPACE_END
