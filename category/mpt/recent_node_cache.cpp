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

#include <category/mpt/recent_node_cache.hpp>

#include <category/core/assert.h>
#include <category/core/log.hpp>
#include <category/core/util/stopwatch.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/update.hpp>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

namespace
{
    using Key = RecentNodeCache::Key;

    // The keys an update list writes at cache_recent() positions, relative to
    // the recorded-key prefix, unless there are more than `budget`.
    class WriteKeys
    {
        StateMachine &sm_;
        uint64_t budget_;

        bool take()
        {
            if (budget_ == 0) {
                over_budget = true;
                return false;
            }
            --budget_;
            ++count;
            return true;
        }

        std::vector<Key> keys_of(UpdateList const &updates)
        {
            std::vector<Key> keys;
            for (Update const &u : updates) {
                if (!take()) {
                    break;
                }
                keys.push_back(
                    Key{.path = Nibbles{u.key}, .next = keys_of(u.next)});
            }
            return keys;
        }

        // `updates` start at the end of the recorded-key prefix.
        void below_prefix(UpdateList const &updates)
        {
            for (Update const &u : updates) {
                sm_.down(u.key);
                if (sm_.cache_recent() && take()) {
                    keys.push_back(
                        Key{.path = Nibbles{u.key}, .next = keys_of(u.next)});
                }
                sm_.up(u.key.nibble_size());
                if (over_budget) {
                    return;
                }
            }
        }

    public:
        std::vector<Key> keys;
        uint64_t count{0};
        bool over_budget{false};

        WriteKeys(StateMachine &sm, uint64_t const budget)
            : sm_{sm}
            , budget_{budget}
        {
        }

        // `updates` start `depth` nibbles below the root, short of the end of
        // the recorded-key prefix; `first` is the first of those nibbles.
        void collect(
            UpdateList const &updates, size_t const depth,
            std::optional<unsigned char> const first)
        {
            for (Update const &u : updates) {
                size_t const end = depth + u.key.nibble_size();
                if (end == 0) {
                    collect(u.next, 0, std::nullopt);
                }
                else if (std::optional<size_t> const prefix_len =
                             sm_.recent_key_prefix_len(
                                 first.value_or(u.key.get(0)));
                         prefix_len.has_value()) {
                    sm_.down(u.key);
                    if (end < *prefix_len) {
                        collect(u.next, end, first.value_or(u.key.get(0)));
                    }
                    else if (end == *prefix_len) {
                        below_prefix(u.next);
                    }
                    else if (sm_.cache_recent() && take()) {
                        keys.push_back(Key{
                            .path = Nibbles{u.key.substr(
                                static_cast<unsigned>(*prefix_len - depth))},
                            .next = keys_of(u.next)});
                    }
                    sm_.up(u.key.nibble_size());
                }
                if (over_budget) {
                    return;
                }
            }
        }
    };

    class Drop
    {
        StateMachine &sm_;
        int64_t const version_;
        std::vector<Node::SharedPtr> &detached_;
        // Finalized and proposal sections share subtries.
        std::vector<Node const *> walked_from_;

        // sm_ is at the end of `child`'s path.
        bool detachable(Node const &parent, Node const &child) const
        {
            // Upsert keeps an only child in memory whatever its position.
            return !sm_.cache() && parent.number_of_children() > 1 &&
                   (child.version <= version_ || !sm_.cache_recent());
        }

        // `path` starts at the end of `start`'s path, which sm_ is at.
        void along(
            Node &start, NibblesView const path,
            std::span<Key const> const next)
        {
            Node *node = &start;
            unsigned i = 0;
            size_t descended = 0;
            while (i < path.nibble_size()) {
                unsigned char const branch = path.get(i);
                if ((node->mask & (1u << branch)) == 0) {
                    break;
                }
                unsigned const index = node->to_child_index(branch);
                Node::SharedPtr const &child = node->next(index);
                if (!child) {
                    break;
                }
                ++visited;
                NibblesView const child_path = child->path_nibble_view();
                sm_.down(branch);
                sm_.down(child_path);
                descended += 1 + child_path.nibble_size();
                if (detachable(*node, *child)) {
                    detached_.push_back(node->move_next(index));
                    break;
                }
                if (next.empty() &&
                    i + 1 + child_path.nibble_size() == path.nibble_size()) {
                    break;
                }
                if (!path.substr(i + 1).starts_with(child_path)) {
                    break;
                }
                i += 1 + child_path.nibble_size();
                node = child.get();
            }
            if (i == path.nibble_size()) {
                for (Key const &key : next) {
                    along(*node, key.path, key.next);
                }
            }
            sm_.up(descended);
        }

        // The recorded-key prefix ends `consumed.nibble_size()` nibbles before
        // the end of `node`'s path, which sm_ is at.
        void walk_from(
            Node &node, NibblesView const consumed,
            std::span<Key const> const keys)
        {
            if (std::ranges::find(walked_from_, &node) != walked_from_.end()) {
                return;
            }
            walked_from_.push_back(&node);
            for (Key const &key : keys) {
                NibblesView const path{key.path};
                if (path.starts_with(consumed)) {
                    along(
                        node,
                        path.substr(
                            static_cast<unsigned>(consumed.nibble_size())),
                        key.next);
                }
            }
        }

        // `node` ends `depth` nibbles below the root, short of the end of the
        // recorded-key prefix; `first` is the first of those nibbles.
        void below_root(
            Node &node, size_t const depth,
            std::optional<unsigned char> const first,
            std::span<Key const> const keys)
        {
            for (auto const [index, branch] : NodeChildrenRange(node.mask)) {
                Node::SharedPtr const &child = node.next(index);
                if (!child) {
                    continue;
                }
                std::optional<size_t> const prefix_len =
                    sm_.recent_key_prefix_len(first.value_or(branch));
                if (!prefix_len.has_value()) {
                    continue;
                }
                if (*prefix_len <= depth) {
                    walk_from(node, {}, keys);
                    return;
                }
                NibblesView const child_path = child->path_nibble_view();
                size_t const child_depth = depth + 1 + child_path.nibble_size();
                sm_.down(branch);
                sm_.down(child_path);
                if (*prefix_len <= child_depth) {
                    NibblesView const consumed = child_path.substr(
                        static_cast<unsigned>(*prefix_len - depth - 1));
                    // Walks start below the prefix, so none reaches a node
                    // that starts inside it.
                    if (!consumed.empty() && detachable(node, *child) &&
                        std::ranges::any_of(keys, [consumed](Key const &key) {
                            return NibblesView{key.path}.starts_with(consumed);
                        })) {
                        detached_.push_back(node.move_next(index));
                    }
                    else {
                        walk_from(*child, consumed, keys);
                    }
                }
                else {
                    below_root(
                        *child, child_depth, first.value_or(branch), keys);
                }
                sm_.up(1 + child_path.nibble_size());
            }
        }

    public:
        uint64_t visited{0};

        Drop(
            StateMachine &sm, int64_t const version,
            std::vector<Node::SharedPtr> &detached)
            : sm_{sm}
            , version_{version}
            , detached_{detached}
        {
        }

        // sm_ is at the root position.
        void run(Node &root, std::span<Key const> const keys)
        {
            NibblesView const path = root.path_nibble_view();
            sm_.down(path);
            if (path.empty()) {
                below_root(root, 0, std::nullopt, keys);
            }
            else if (std::optional<size_t> const prefix_len =
                         sm_.recent_key_prefix_len(path.get(0));
                     prefix_len.has_value()) {
                if (*prefix_len <= path.nibble_size()) {
                    walk_from(
                        root,
                        path.substr(static_cast<unsigned>(*prefix_len)),
                        keys);
                }
                else {
                    below_root(root, path.nibble_size(), path.get(0), keys);
                }
            }
            sm_.up(path.nibble_size());
        }
    };
}

void RecentNodeCache::configure(RecentNodeCacheConfig const &config)
{
    config_ = config;
    pending_ = Recorded{};
    pending_finds_.clear();
    pending_count_ = 0;
    keeping_ = false;
    window_.clear();
    window_bytes_ = 0;
    last_version_.reset();
}

void RecentNodeCache::close_pending(StateMachine const &sm)
{
    for (Nibbles const &key : std::exchange(pending_finds_, {})) {
        std::optional<size_t> const prefix_len =
            sm.recent_key_prefix_len(key.get(0));
        if (prefix_len.has_value() && key.nibble_size() > *prefix_len) {
            pending_.keys.push_back(
                Key{.path = key.substr(static_cast<unsigned>(*prefix_len)),
                    .next = {}});
        }
    }
    pending_count_ = 0;
    if (pending_.keys.empty() && pending_.bytes == 0) {
        pending_ = Recorded{};
        return;
    }
    window_bytes_ += pending_.bytes;
    window_.push_back(std::exchange(pending_, Recorded{}));
}

void RecentNodeCache::record_writes(
    UpdateList const &updates, StateMachine &sm, uint64_t const version)
{
    keeping_ = false;
    if (!enabled()) {
        return;
    }
    MONAD_ASSERT(
        version <= static_cast<uint64_t>(std::numeric_limits<int64_t>::max()));
    if (last_version_ != version) {
        pending_.version =
            static_cast<int64_t>(last_version_.value_or(version));
        close_pending(sm);
        last_version_ = version;
    }
    WriteKeys writes{sm, config_.max_keys_per_version - pending_count_};
    writes.collect(updates, 0, std::nullopt);
    if (writes.over_budget) {
        pending_.partial = true;
        return;
    }
    keeping_ = true;
    pending_count_ += writes.count;
    std::ranges::move(writes.keys, std::back_inserter(pending_.keys));
}

bool RecentNodeCache::keep(size_t const bytes) noexcept
{
    if (!keeping_ || pending_.bytes + bytes > config_.max_bytes) {
        return false;
    }
    pending_.bytes += bytes;
    return true;
}

bool RecentNodeCache::recorded_in_full(int64_t const version) const
{
    if (last_version_.has_value() &&
        version == static_cast<int64_t>(*last_version_)) {
        return !pending_.partial;
    }
    auto const it = std::ranges::find(window_, version, &Recorded::version);
    return it != window_.end() && !it->partial;
}

// The copy keeps the original's version, and so the path of a key that
// version wrote; that key's walk reaches the copy.
bool RecentNodeCache::keep_copy(int64_t const version, size_t const bytes)
{
    return keeping_ && recorded_in_full(version) && keep(bytes);
}

bool RecentNodeCache::record_find(NibblesView const key)
{
    if (!enabled()) {
        return true;
    }
    if (key.empty() || pending_count_ >= config_.max_keys_per_version) {
        return false;
    }
    pending_finds_.emplace_back(key);
    ++pending_count_;
    return true;
}

void RecentNodeCache::drop_oldest(Node &root, StateMachine const &sm)
{
    Recorded const recorded = std::move(window_.front());
    window_.pop_front();
    window_bytes_ -= recorded.bytes;

    Stopwatch<std::chrono::microseconds> const timer;
    std::vector<Node::SharedPtr> detached;
    std::unique_ptr<StateMachine> const walker_sm = sm.clone();
    Drop drop{*walker_sm, recorded.version, detached};
    drop.run(root, recorded.keys);
    size_t const evicted = detached.size();
    detached.clear();
    LOG_DEBUG(
        "recent nodes leave version={} keys={} visited={} detached={} us={}",
        recorded.version,
        recorded.keys.size(),
        drop.visited,
        evicted,
        timer.elapsed().count());
}

void RecentNodeCache::after_upsert(
    Node &root, StateMachine const &sm, uint64_t const version)
{
    keeping_ = false;
    if (!enabled()) {
        return;
    }
    // A node written at version w serves the upserts of the next
    // window_versions versions.
    int64_t const leaving =
        static_cast<int64_t>(version) -
        static_cast<int64_t>(std::min<uint64_t>(
            config_.window_versions,
            static_cast<uint64_t>(std::numeric_limits<int64_t>::max())));
    // Nodes of the current version may not have reached disk yet.
    while (!window_.empty() &&
           window_.front().version < static_cast<int64_t>(version) &&
           (window_.front().version <= leaving ||
            window_bytes_ + pending_.bytes > config_.max_bytes)) {
        drop_oldest(root, sm);
    }
}

MONAD_MPT_NAMESPACE_END
