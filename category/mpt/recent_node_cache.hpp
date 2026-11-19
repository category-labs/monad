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

#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/update.hpp>

#include <cstddef>
#include <cstdint>
#include <deque>
#include <limits>
#include <optional>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

class Node;
struct StateMachine;

struct RecentNodeCacheConfig
{
    // Versions a node written at a StateMachine::cache_recent() position stays
    // in memory after the write. 0 disables retention and recording.
    uint64_t window_versions{0};
    // Bound on the bytes of nodes written in the window; over it, the oldest
    // versions leave the window early, and the current version keeps no more.
    uint64_t max_bytes{std::numeric_limits<uint64_t>::max()};
    // Bound on the keys one version records, writes and finds together. An
    // upsert whose keys do not fit keeps none of its nodes, such as a
    // snapshot load's batches, and a find that does not fit attaches none.
    uint64_t max_keys_per_version{1 << 16};
};

// Keeps nodes upsert writes at cache_recent() positions outside cache() in
// memory for a window of versions, and holds nodes a find attaches outside
// cache() for the same window.
//
// Each version records the keys its upserts wrote at cache_recent() positions
// and the keys finds looked up since the previous version, relative to
// StateMachine::recent_key_prefix_len(). When a version leaves the window,
// each of its keys is walked down from every in-memory position that prefix
// ends at, and the first node outside cache() on the path that is no newer
// than that version, or not at a cache_recent() position, is detached. A
// node's version is the newest write in its subtrie, so a node written since
// stays for the later version's walk.
class RecentNodeCache
{
public:
    struct Key
    {
        Nibbles path;
        // Continue from the end of `path`.
        std::vector<Key> next;
    };

private:
    struct Recorded
    {
        int64_t version{0};
        std::vector<Key> keys;
        // Of nodes kept at write time; nodes written again since count twice.
        uint64_t bytes{0};
    };

    RecentNodeCacheConfig config_{};
    Recorded pending_{};
    // From the root; resolved against the upsert's machine when the version
    // closes, as finds carry none.
    std::vector<Nibbles> pending_finds_{};
    // Keys in pending_ and pending_finds_, nested ones included. pending_
    // collects the current version and the finds after its upserts.
    uint64_t pending_count_{0};
    // The current upsert's keys were recorded.
    bool keeping_{false};
    std::deque<Recorded> window_{};
    uint64_t window_bytes_{0};
    std::optional<uint64_t> last_version_{};

    // Moves the current version's keys into the window.
    void close_pending(StateMachine const &sm);
    void drop_oldest(Node &root, StateMachine const &sm);

public:
    void configure(RecentNodeCacheConfig const &);

    bool enabled() const noexcept
    {
        return config_.window_versions != 0;
    }

    // Before an upsert. `sm` must be at the root position of `updates`.
    void record_writes(
        UpdateList const &updates, StateMachine &sm, uint64_t version);

    // Whether the current upsert keeps a node of `bytes` it wrote at a
    // cache_recent() position outside cache().
    bool keep(size_t bytes) noexcept;

    // Whether a find of `key`, which starts at the root, may attach the nodes
    // it loads.
    bool record_find(NibblesView key);

    // Must run on the thread that owns the trie, with no find or upsert in
    // flight. `sm` must be at the root position.
    void after_upsert(Node &root, StateMachine const &sm, uint64_t version);
};

MONAD_MPT_NAMESPACE_END
