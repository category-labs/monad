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
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/bytes.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/space_counters.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <thread>
#include <utility>
#include <vector>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
    namespace
    {
        constexpr unsigned walk_reads_in_flight = 512; // per walk thread
        // Subtries handed out per walk thread, so that the threads finish
        // close together although subtrie sizes vary widely.
        constexpr size_t walk_subtries_per_thread = 32;

        // On cold mainnet state the walk is CPU-bound per thread and scales
        // near linearly up to 8 threads.
        unsigned walk_threads()
        {
            return std::clamp(std::thread::hardware_concurrency() / 8, 1u, 8u);
        }

        uint64_t clamped_sum(
            uint64_t const live, uint64_t const written,
            uint64_t const superseded) noexcept
        {
            uint64_t const grown = live + written;
            return grown > superseded ? grown - superseded : 0;
        }

        using chunk_list = DbMetadataContext::chunk_list;

        // Atomic: the walk runs while the writer moves chunks between lists.
        chunk_list list_of(UpdateAux const &aux, uint32_t const id) noexcept
        {
            auto const info = aux.metadata_ctx().main()->atomic_load_chunk_info(
                id, std::memory_order_acquire);
            if (info.in_fast_list) {
                return chunk_list::fast;
            }
            return info.in_slow_list ? chunk_list::slow : chunk_list::free;
        }

        void add_to_list(
            list_bytes &bytes, chunk_list const list,
            uint32_t const size) noexcept
        {
            (list == chunk_list::fast ? bytes.fast : bytes.slow) += size;
        }

        std::unique_ptr<StateMachine>
        clone_machine(StateMachine const *const machine)
        {
            return machine != nullptr ? machine->clone() : nullptr;
        }

        // Adds the bytes of every node that a traversal visits below its
        // start node to `bytes`, by the list of each node's chunk. Clones
        // share `bytes` and `failed`, so one traversal must stay on one
        // thread.
        class LiveBytesMachine final : public TraverseMachine
        {
            UpdateAux const *aux_;
            list_bytes *bytes_;
            bool *failed_;
            std::function<bool()> const *keep_going_;
            std::unique_ptr<StateMachine> machine_; // null: everything counts
            chunk_list next_list_{chunk_list::free};

        public:
            LiveBytesMachine(
                UpdateAux const &aux, list_bytes &bytes, bool &failed,
                std::function<bool()> const &keep_going,
                std::unique_ptr<StateMachine> machine)
                : aux_{&aux}
                , bytes_{&bytes}
                , failed_{&failed}
                , keep_going_{&keep_going}
                , machine_{std::move(machine)}
            {
            }

            LiveBytesMachine(LiveBytesMachine const &other)
                : TraverseMachine{other}
                , aux_{other.aux_}
                , bytes_{other.bytes_}
                , failed_{other.failed_}
                , keep_going_{other.keep_going_}
                , machine_{clone_machine(other.machine_.get())}
                , next_list_{other.next_list_}
            {
            }

            LiveBytesMachine &operator=(LiveBytesMachine const &) = delete;

            // Called just before the traversal visits or reads the child.
            virtual bool
            should_visit(Node const &node, unsigned char const branch) override
            {
                next_list_ =
                    list_of(*aux_, node.fnext(node.to_child_index(branch)).id);
                if (next_list_ == chunk_list::free) {
                    *failed_ = true;
                }
                return !*failed_;
            }

            virtual bool
            down(unsigned char const branch, Node const &node) override
            {
                if (branch == INVALID_BRANCH) {
                    return !machine_ || machine_->counts_live_bytes_below();
                }
                if (*failed_ || (*keep_going_ && !(*keep_going_)())) {
                    *failed_ = true;
                    return false;
                }
                add_to_list(*bytes_, next_list_, node.get_disk_size());
                if (!machine_) {
                    return true;
                }
                machine_->down(branch);
                machine_->down(node.path_nibble_view());
                if (machine_->counts_live_bytes_below()) {
                    return true;
                }
                // The traversal does not call up() after a false down().
                machine_->up(1 + node.path_nibbles_len());
                return false;
            }

            virtual void
            up(unsigned char const branch, Node const &node) override
            {
                if (machine_ && branch != INVALID_BRANCH) {
                    machine_->up(1 + node.path_nibbles_len());
                }
            }

            virtual std::unique_ptr<TraverseMachine> clone() const override
            {
                return std::make_unique<LiveBytesMachine>(*this);
            }
        };

        // Only the nodes below `node` remain to be counted.
        struct subtrie
        {
            Node::SharedPtr node;
            std::unique_ptr<StateMachine> machine; // positioned at `node`
        };

        // Replaces `subtries` by their children, counting the children, until
        // there are at least `target` of them or none are left.
        bool split_subtries(
            UpdateAux const &aux, uint64_t const version, timeline_id const tid,
            std::function<bool()> const &keep_going, size_t const target,
            std::vector<subtrie> &subtries, list_bytes &bytes)
        {
            while (!subtries.empty() && subtries.size() < target) {
                std::vector<subtrie> children;
                for (auto const &[node, machine] : subtries) {
                    if (machine && !machine->counts_live_bytes_below()) {
                        continue;
                    }
                    for (auto const [index, branch] :
                         NodeChildrenRange(node->mask)) {
                        if (keep_going && !keep_going()) {
                            return false;
                        }
                        auto const offset = node->fnext(index);
                        auto const list = list_of(aux, offset.id);
                        if (list == chunk_list::free) {
                            return false;
                        }
                        Node::SharedPtr child =
                            read_node_blocking(aux, offset, version, tid);
                        if (!child) {
                            return false;
                        }
                        add_to_list(bytes, list, child->get_disk_size());
                        auto child_machine = clone_machine(machine.get());
                        if (child_machine) {
                            child_machine->down(branch);
                            child_machine->down(child->path_nibble_view());
                        }
                        children.push_back(
                            {.node = std::move(child),
                             .machine = std::move(child_machine)});
                    }
                }
                subtries = std::move(children);
            }
            return true;
        }

        // Each thread traverses the subtries it takes, with its own read-only
        // view of the pool and its own i/o ring.
        bool traverse_subtries(
            UpdateAux const &aux, uint64_t const version, timeline_id const tid,
            std::function<bool()> const &keep_going, unsigned const threads,
            std::vector<subtrie> const &subtries, list_bytes &bytes)
        {
            std::atomic<size_t> next{0};
            std::atomic<bool> failed{false};
            std::vector<list_bytes> found(threads);
            {
                std::vector<std::jthread> workers;
                workers.reserve(threads);
                for (unsigned t = 0; t < threads; ++t) {
                    workers.emplace_back([&, t] {
                        auto pool = aux.io->storage_pool().clone_as_read_only();
                        monad::io::Ring ring{
                            monad::io::RingConfig{walk_reads_in_flight}};
                        monad::io::Buffers buffers =
                            monad::io::make_buffers_for_read_only(
                                ring,
                                walk_reads_in_flight,
                                MONAD_ASYNC_NAMESPACE::AsyncIO::
                                    MONAD_IO_BUFFERS_READ_SIZE);
                        MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, buffers};
                        UpdateAux reader{io};
                        for (size_t i = next++;
                             i < subtries.size() && !failed.load();
                             i = next++) {
                            bool subtrie_failed = false;
                            LiveBytesMachine machine{
                                reader,
                                found[t],
                                subtrie_failed,
                                keep_going,
                                clone_machine(subtries[i].machine.get())};
                            if (!preorder_traverse_ondisk(
                                    reader,
                                    subtries[i].node,
                                    machine,
                                    version,
                                    tid,
                                    walk_reads_in_flight) ||
                                subtrie_failed) {
                                failed = true;
                            }
                        }
                    });
                }
            }
            if (failed.load()) {
                return false;
            }
            for (auto const &f : found) {
                bytes.fast += f.fast;
                bytes.slow += f.slow;
            }
            return true;
        }
    }

    void space_delta::add(space_delta const &other) noexcept
    {
        written.fast += other.written.fast;
        written.slow += other.written.slow;
        superseded.fast += other.superseded.fast;
        superseded.slow += other.superseded.slow;
        complete = complete && other.complete;
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

    void settlement_table::discard(bytes32_t const &key)
    {
        entries_.erase(key);
    }

    size_t settlement_table::size() const noexcept
    {
        return entries_.size();
    }

    std::optional<list_bytes> bytes_below(
        UpdateAux &aux, Node const &node, uint64_t const version,
        timeline_id const tid, StateMachine const *const machine)
    {
        list_bytes bytes{};
        bool failed = false;
        std::function<bool()> const keep_going;
        LiveBytesMachine traverse{
            aux, bytes, failed, keep_going, clone_machine(machine)};
        if (!preorder_traverse_blocking(aux, node, traverse, version, tid) ||
            failed) {
            return std::nullopt;
        }
        return bytes;
    }

    std::optional<list_bytes> walk_live_bytes(
        UpdateAux const &aux, chunk_offset_t const root, uint64_t const version,
        timeline_id const tid, NibblesView const prefix,
        StateMachine const *const machine,
        std::function<bool()> const &keep_going)
    {
        Node::SharedPtr node = read_node_blocking(aux, root, version, tid);
        if (!node) {
            return std::nullopt;
        }
        auto start_machine = clone_machine(machine);
        if (start_machine) {
            start_machine->down(node->path_nibble_view());
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
            if (start_machine) {
                start_machine->down(branch);
                start_machine->down(node->path_nibble_view());
            }
        }
        unsigned const threads = walk_threads();
        list_bytes bytes{};
        std::vector<subtrie> subtries;
        subtries.push_back(
            {.node = std::move(node), .machine = std::move(start_machine)});
        if (!split_subtries(
                aux,
                version,
                tid,
                keep_going,
                threads * walk_subtries_per_thread,
                subtries,
                bytes) ||
            !traverse_subtries(
                aux,
                version,
                tid,
                keep_going,
                static_cast<unsigned>(
                    std::min<size_t>(threads, subtries.size())),
                subtries,
                bytes)) {
            return std::nullopt;
        }
        return bytes;
    }
}

MONAD_MPT_NAMESPACE_END
