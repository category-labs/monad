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

#include <category/async/config.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/space_counters.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
    namespace
    {
        uint64_t clamped_sum(
            uint64_t const live, uint64_t const written,
            uint64_t const superseded) noexcept
        {
            uint64_t const grown = live + written;
            return grown > superseded ? grown - superseded : 0;
        }

        void add_to_list(
            UpdateAux const &aux, list_bytes &bytes,
            MONAD_ASYNC_NAMESPACE::chunk_offset_t const offset,
            uint32_t const size)
        {
            if (aux.metadata_ctx().main()->at(offset.id)->in_fast_list) {
                bytes.fast += size;
            }
            else {
                bytes.slow += size;
            }
        }
    }

    void space_delta::add(space_delta const &other) noexcept
    {
        written.fast += other.written.fast;
        written.slow += other.written.slow;
        superseded.fast += other.superseded.fast;
        superseded.slow += other.superseded.slow;
    }

    list_bytes apply(list_bytes const live, space_delta const &delta) noexcept
    {
        return {
            .fast = clamped_sum(
                live.fast, delta.written.fast, delta.superseded.fast),
            .slow = clamped_sum(
                live.slow, delta.written.slow, delta.superseded.slow)};
    }

    void settlement_table::add(
        bytes32_t const &key, uint64_t const version, space_delta const &delta)
    {
        auto [it, inserted] =
            entries_.try_emplace(key, entry{.version = version, .delta = {}});
        it->second.version = std::max(it->second.version, version);
        it->second.delta.add(delta);
    }

    std::optional<space_delta>
    settlement_table::settle(uint64_t const version, bytes32_t const &winner)
    {
        std::optional<space_delta> won;
        if (auto const it = entries_.find(winner); it != entries_.end()) {
            won = it->second.delta;
        }
        std::erase_if(entries_, [version](auto const &item) {
            return item.second.version <= version;
        });
        return won;
    }

    size_t settlement_table::size() const noexcept
    {
        return entries_.size();
    }

    std::optional<list_bytes> walk_live_bytes(
        UpdateAux const &aux, MONAD_ASYNC_NAMESPACE::chunk_offset_t const root,
        uint64_t const version, timeline_id const tid, NibblesView const prefix,
        std::function<bool()> const &keep_going)
    {
        Node::SharedPtr node = read_node_blocking(aux, root, version, tid);
        if (!node) {
            return std::nullopt;
        }
        unsigned consumed = 0;
        while (consumed < prefix.nibble_size()) {
            NibblesView const path = node->path_nibble_view();
            unsigned const n = std::min(
                static_cast<unsigned>(path.nibble_size()),
                static_cast<unsigned>(prefix.nibble_size()) - consumed);
            if (path.substr(0, n) != prefix.substr(consumed, n)) {
                return list_bytes{};
            }
            consumed += n;
            if (consumed == prefix.nibble_size()) {
                break;
            }
            auto const branch = prefix.get(consumed);
            if (!(node->mask & (1u << branch))) {
                return list_bytes{};
            }
            ++consumed;
            node = read_node_blocking(
                aux, node->fnext(node->to_child_index(branch)), version, tid);
            if (!node) {
                return std::nullopt;
            }
        }
        list_bytes live{};
        std::vector<MONAD_ASYNC_NAMESPACE::chunk_offset_t> pending;
        pending.reserve(node->number_of_children());
        for (unsigned i = 0; i < node->number_of_children(); ++i) {
            pending.push_back(node->fnext(i));
        }
        while (!pending.empty()) {
            if (keep_going && !keep_going()) {
                return std::nullopt;
            }
            auto const offset = pending.back();
            pending.pop_back();
            Node::SharedPtr const child =
                read_node_blocking(aux, offset, version, tid);
            if (!child) {
                return std::nullopt;
            }
            add_to_list(aux, live, offset, child->get_disk_size());
            for (unsigned i = 0; i < child->number_of_children(); ++i) {
                pending.push_back(child->fnext(i));
            }
        }
        return live;
    }
}

MONAD_MPT_NAMESPACE_END
