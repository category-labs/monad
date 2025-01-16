#pragma once

#include <monad/async/config.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/detail/collected_stats.hpp>
#include <monad/mpt/detail/db_metadata.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/node_cursor.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/upward_tnode.hpp>
#include <monad/mpt/util.hpp>

#include <monad/async/io.hpp>
#include <monad/async/io_senders.hpp>

#include <monad/core/tl_tid.h>
#include <monad/core/unordered_map.hpp>

#ifdef __clang__
    #pragma clang diagnostic push
    #pragma clang diagnostic ignored "-Wdeprecated-declarations"
#endif
#include <boost/fiber/future.hpp>
#ifdef __clang__
    #pragma clang diagnostic pop
#endif

#include <atomic>
#include <bit>
#include <cstdint>
#include <functional>
#include <vector>

// temporary
#include "detail/boost_fiber_workarounds.hpp"

MONAD_MPT_NAMESPACE_BEGIN

template <class T>
concept lockable_or_void = std::is_void_v<T> || requires(T x) {
    x.lock();
    x.unlock();
};

class Node;

struct write_operation_io_receiver
{
    size_t should_be_written;

    // Node *parent{nullptr};

    explicit constexpr write_operation_io_receiver(
        size_t const should_be_written_)
        : should_be_written(should_be_written_)
    {
    }

    void set_value(
        MONAD_ASYNC_NAMESPACE::erased_connected_operation *,
        MONAD_ASYNC_NAMESPACE::write_single_buffer_sender::result_type res)
    {
        MONAD_ASSERT(res);
        MONAD_ASSERT(res.assume_value().get().size() == should_be_written);
        res.assume_value()
            .get()
            .reset(); // release i/o buffer before initiating other work
        // TODO: when adding upsert_sender
        // if (parent->current_process_updates_sender_ != nullptr) {
        //     parent->current_process_updates_sender_
        //         ->notify_write_operation_completed_(rawstate);
        // }
    }

    void reset(size_t const should_be_written_)
    {
        should_be_written = should_be_written_;
    }
};

using node_writer_unique_ptr_type =
    MONAD_ASYNC_NAMESPACE::AsyncIO::connected_operation_unique_ptr_type<
        MONAD_ASYNC_NAMESPACE::write_single_buffer_sender,
        write_operation_io_receiver>;

using MONAD_ASYNC_NAMESPACE::receiver;

struct read_short_update_sender
    : MONAD_ASYNC_NAMESPACE::read_single_buffer_sender
{
    template <receiver Receiver>
    constexpr read_short_update_sender(Receiver const &receiver)
        : read_single_buffer_sender(receiver.rd_offset, receiver.bytes_to_read)
    {
        MONAD_DEBUG_ASSERT(
            receiver.bytes_to_read <=
            MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE);
    }
};

class read_long_update_sender
    : public MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender
{
    MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender::buffer_type buffer_;

public:
    template <receiver Receiver>
    read_long_update_sender(Receiver const &receiver)
        : MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender(
              receiver.rd_offset, {&buffer_, 1})
        , buffer_(
              (std::byte *)aligned_alloc(
                  DISK_PAGE_SIZE, receiver.bytes_to_read),
              receiver.bytes_to_read)
    {
        MONAD_DEBUG_ASSERT(
            receiver.bytes_to_read >
            MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE);
        MONAD_ASSERT(buffer_.data() != nullptr);
    }

    read_long_update_sender(read_long_update_sender &&o) noexcept
        : MONAD_ASYNC_NAMESPACE::read_multiple_buffer_sender(std::move(o))
        , buffer_(o.buffer_)
    {
        this->reset(this->offset(), {&buffer_, 1});
        o.buffer_ = {};
    }

    read_long_update_sender &operator=(read_long_update_sender &&o) noexcept

    {
        if (this != &o) {
            this->~read_long_update_sender();
            new (this) read_long_update_sender(std::move(o));
        }
        return *this;
    }

    ~read_long_update_sender()
    {
        if (buffer_.data() != nullptr) {
            ::free(buffer_.data());
            buffer_ = {};
        }
    }
};

chunk_offset_t
async_write_node_set_spare(UpdateAuxImpl &, Node &, bool is_fast);

chunk_offset_t
write_new_root_node(UpdateAuxImpl &, Node &root, uint64_t version);

node_writer_unique_ptr_type
replace_node_writer(UpdateAuxImpl &, node_writer_unique_ptr_type const &);

// \class Auxiliaries for triedb update
class UpdateAuxImpl
{
    uint32_t initial_insertion_count_on_pool_creation_{0};
    bool enable_dynamic_history_length_{true};

    struct db_metadata_
    {
        detail::db_metadata *main{nullptr};
        std::span<chunk_offset_t>
            root_offsets; // if not-null, mmap of DB version ring buffer storage
    } db_metadata_[2]; // two copies, to prevent sudden process
                       // exits making the DB irretrievable

    void reset_node_writers();

    void advance_compact_offsets(Node &prev_root, uint64_t version);

    void free_compacted_chunks();

    void erase_version(uint64_t const version);

    /* Calculate the version up to which the database will automatically expire
    entries (referred to as "auto_expire" in code names).

    Currently, the db auto-expires at most 2 blocks per upsert as a
    temporary workaround to reduce the sudden increase in auto-expiration
    workload during upserts that significantly shorten the history length.

    TODO: Develop a more efficient and scalable mechanism for auto-expiration
    throttling. The goal is to ensure stable database commit times despite
    varying block loads. */
    int64_t calc_auto_expire_version() noexcept;

    void set_auto_expire_version_metadata(int64_t) noexcept;

    void update_disk_growth_data();

    /******** Compaction ********/
    uint32_t chunks_to_remove_before_count_fast_{0};
    uint32_t chunks_to_remove_before_count_slow_{0};
    // speed control var
    compact_virtual_chunk_offset_t last_block_end_offset_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_end_offset_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_disk_growth_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t last_block_disk_growth_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    // compaction range
    compact_virtual_chunk_offset_t compact_offset_range_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t compact_offset_range_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};

    std::optional<pid_t> current_upsert_tid_; // used to detect what thread is
                                              // currently upserting
    bool alternate_slow_fast_writer_{false};
    bool can_write_to_fast_{true};

    virtual void lock_unique_() const = 0;

    virtual void unlock_unique_() const noexcept = 0;

    virtual void lock_shared_() const = 0;

    virtual void unlock_shared_() const noexcept = 0;

    virtual bool upgrade_shared_to_unique_() const noexcept = 0;

    virtual bool downgrade_unique_to_shared_() const noexcept = 0;

    virtual void on_read_only_init_with_dirty_bit() noexcept {};

protected:
    uint64_t upsert_call_count_{0};

    class shared_lock_holder_;
    friend class shared_lock_holder_;

    class shared_lock_holder_
    {
        friend class MONAD_MPT_NAMESPACE::UpdateAuxImpl;
        UpdateAuxImpl const *parent_{nullptr};
        bool const was_atomic_;

        explicit constexpr shared_lock_holder_(
            UpdateAuxImpl const *parent, bool was_atomic)
            : parent_(parent)
            , was_atomic_(was_atomic)
        {
        }

    public:
        shared_lock_holder_(shared_lock_holder_ const &) = delete;

        shared_lock_holder_(shared_lock_holder_ &&o)
            : parent_(o.parent_)
            , was_atomic_(o.was_atomic_)
        {
            o.parent_ = nullptr;
        }

        ~shared_lock_holder_()
        {
            if (parent_ != nullptr) {
                parent_->unlock_shared_();
            }
        }

        shared_lock_holder_ &operator=(shared_lock_holder_ const &) = delete;

        shared_lock_holder_ &operator=(shared_lock_holder_ &&o) noexcept
        {
            if (this != &o) {
                this->~shared_lock_holder_();
                new (this) shared_lock_holder_(std::move(o));
            }
            return *this;
        }

        bool downgrade_was_atomic() const noexcept
        {
            return was_atomic_;
        }

        auto upgrade() const
        {
            class holder2
            {
                shared_lock_holder_ const *parent_;
                uint64_t const initial_upsert_call_count_;
                bool const was_atomic_;

            public:
                explicit constexpr holder2(shared_lock_holder_ const *parent)
                    : parent_(parent)
                    , initial_upsert_call_count_(
                          parent_->parent_->upsert_call_count_)
                    , was_atomic_(parent_->parent_->upgrade_shared_to_unique_())
                {
                    if (!was_atomic_) {
                        parent_->parent_->unlock_shared_();
                        // an upsert could begin and complete now
                        // theoretically causing nodes to get freed
                        parent_->parent_->lock_unique_();
                        MONAD_ASSERT(
                            initial_upsert_call_count_ ==
                            parent_->parent_->upsert_call_count_);
                    }
                }

                holder2(holder2 const &) = delete;

                holder2(holder2 &&o)
                    : parent_(o.parent_)
                    , initial_upsert_call_count_(o.initial_upsert_call_count_)
                    , was_atomic_(o.was_atomic_)
                {
                    o.parent_ = nullptr;
                }

                ~holder2()
                {
                    unlock();
                }

                holder2 &operator=(holder2 const &) = delete;

                holder2 &operator=(holder2 &&o) noexcept
                {
                    if (this != &o) {
                        this->~holder2();
                        new (this) holder2(std::move(o));
                    }
                    return *this;
                }

                bool upgrade_was_atomic() const noexcept
                {
                    return was_atomic_;
                }

                void unlock()
                {
                    if (parent_ != nullptr) {
                        if (was_atomic_) {
                            parent_->parent_->downgrade_unique_to_shared_();
                        }
                        else {
                            parent_->parent_->unlock_unique_();
                            // an upsert could begin and complete now
                            // theoretically causing nodes to get freed
                            parent_->parent_->lock_shared_();
                            MONAD_ASSERT(
                                initial_upsert_call_count_ ==
                                parent_->parent_->upsert_call_count_);
                        }
                        parent_ = nullptr;
                    }
                }
            };

            return holder2{this};
        }
    };

public:
    int64_t curr_upsert_auto_expire_version{0};
    compact_virtual_chunk_offset_t compact_offset_fast{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t compact_offset_slow{
        MIN_COMPACT_VIRTUAL_OFFSET};

    // On disk stuff
    MONAD_ASYNC_NAMESPACE::AsyncIO *io{nullptr};
    node_writer_unique_ptr_type node_writer_fast{};
    node_writer_unique_ptr_type node_writer_slow{};

    detail::TrieUpdateCollectedStats stats;

    UpdateAuxImpl(
        MONAD_ASYNC_NAMESPACE::AsyncIO *io_ = nullptr,
        std::optional<uint64_t> const history_len = {})
    {
        if (io_) {
            set_io(io_, history_len);
        }
    }

    virtual ~UpdateAuxImpl();

    auto unique_lock() const
    {
        class holder
        {
            friend class MONAD_MPT_NAMESPACE::UpdateAuxImpl;
            UpdateAuxImpl const *parent_;

            explicit constexpr holder(UpdateAuxImpl const *parent)
                : parent_(parent)
            {
                parent_->lock_unique_();
            }

        public:
            holder(holder const &) = delete;

            holder(holder &&o)
                : parent_(o.parent_)
            {
                o.parent_ = nullptr;
            }

            ~holder()
            {
                if (parent_ != nullptr) {
                    parent_->unlock_unique_();
                }
            }

            holder &operator=(holder const &) = delete;

            holder &operator=(holder &&o) noexcept
            {
                if (this != &o) {
                    this->~holder();
                    new (this) holder(std::move(o));
                }
                return *this;
            }

            shared_lock_holder_ downgrade() &&
            {
                auto const initial_upsert_call_count =
                    parent_->upsert_call_count_;
                auto const was_atomic = parent_->downgrade_unique_to_shared_();
                if (!was_atomic) {
                    parent_->unlock_unique_();
                    // an upsert could begin and complete now
                    // theoretically causing nodes to get freed
                    parent_->lock_shared_();
                    MONAD_ASSERT(
                        initial_upsert_call_count ==
                        parent_->upsert_call_count_);
                }
                // takes ownership
                shared_lock_holder_ ret{parent_, was_atomic};
                parent_ = nullptr;
                return ret;
            }
        };

        return holder{this};
    }

    shared_lock_holder_ shared_lock() const
    {
        lock_shared_();
        return shared_lock_holder_{this, false};
    }

    auto set_current_upsert_tid()
    {
        class holder
        {
            friend class MONAD_MPT_NAMESPACE::UpdateAuxImpl;
            UpdateAuxImpl *parent_;

            explicit constexpr holder(UpdateAuxImpl *parent)
                : parent_(parent)
            {
                parent_->current_upsert_tid_ = get_tl_tid();
            }

        public:
            holder(holder const &) = delete;

            holder(holder &&o)
                : parent_(o.parent_)
            {
                o.parent_ = nullptr;
            }

            ~holder()
            {
                if (parent_ != nullptr) {
                    parent_->upsert_call_count_++;
                    parent_->current_upsert_tid_ = {};
                }
            }

            holder &operator=(holder const &) = delete;

            holder &operator=(holder &&o) noexcept
            {
                if (this != &o) {
                    this->~holder();
                    new (this) holder(std::move(o));
                }
                return *this;
            }
        };

        return holder{this};
    }

    bool is_current_thread_concurrent_to_upsert() const noexcept
    {
        return current_upsert_tid_.has_value() &&
               *current_upsert_tid_ != get_tl_tid();
    }

    bool is_current_thread_upserting() const noexcept
    {
        return current_upsert_tid_.has_value() &&
               *current_upsert_tid_ == get_tl_tid();
    }

    bool has_upsert_run_since() const noexcept
    {
        return current_upsert_tid_.has_value() &&
               *current_upsert_tid_ != get_tl_tid();
    }

    void set_io(
        MONAD_ASYNC_NAMESPACE::AsyncIO *,
        std::optional<uint64_t> history_length = {});

    void unset_io();

    Node::UniquePtr do_update(
        Node::UniquePtr prev_root, StateMachine &, UpdateList &&,
        uint64_t version, bool compaction = false,
        bool can_write_to_fast = true);

    void adjust_history_length_based_on_disk_usage();
    void move_trie_version_forward(uint64_t src, uint64_t dest);

    // collect and print trie update stats
    void reset_stats();
    void collect_expire_stats(bool is_read);
    void collect_number_nodes_created_stats();
    void collect_compaction_read_stats(
        chunk_offset_t node_offset, unsigned bytes_to_read);
    void collect_compacted_nodes_stats(
        bool const copy_node_for_fast, bool const rewrite_to_fast,
        virtual_chunk_offset_t node_offset, uint32_t node_disk_size);

    void print_update_stats(uint64_t version);

    enum class chunk_list : uint8_t
    {
        free = 0,
        fast = 1,
        slow = 2
    };

    detail::db_metadata const *db_metadata() const noexcept
    {
        return db_metadata_[0].main;
    }

    auto root_offsets(unsigned which = 0) const
    {
        class root_offsets_delegator
        {
            std::atomic_ref<uint64_t> version_lower_bound_;
            std::atomic_ref<uint64_t> next_version_;
            std::span<chunk_offset_t> root_offsets_chunks_;

            void
            update_version_lower_bound_(uint64_t lower_bound = uint64_t(-1))
            {
                auto const version_lower_bound =
                    version_lower_bound_.load(std::memory_order_acquire);
                auto idx = (lower_bound < version_lower_bound)
                               ? lower_bound
                               : version_lower_bound;
                auto const max_version =
                    next_version_.load(std::memory_order_acquire) - 1;
                while (idx < max_version && (*this)[idx] == INVALID_OFFSET) {
                    idx++;
                }
                if (idx != version_lower_bound) {
                    version_lower_bound_.store(idx, std::memory_order_release);
                }
            }

        public:
            explicit root_offsets_delegator(const struct db_metadata_ *m)
                : version_lower_bound_(
                      m->main->root_offsets.version_lower_bound_)
                , next_version_(m->main->root_offsets.next_version_)
                , root_offsets_chunks_(
                      m->root_offsets.empty()
                          ? std::span<chunk_offset_t>(
                                m->main->root_offsets.storage_.arr)
                          : std::span<chunk_offset_t>(m->root_offsets))
            {
                MONAD_DEBUG_ASSERT(
                    root_offsets_chunks_.size() ==
                    1ULL
                        << (63 -
                            std::countl_zero(root_offsets_chunks_.size())));
            }

            size_t capacity() const noexcept
            {
                return root_offsets_chunks_.size();
            }

            void push(chunk_offset_t const o) noexcept
            {
                auto const wp = next_version_.load(std::memory_order_relaxed);
                auto const next_wp = wp + 1;
                MONAD_ASSERT(next_wp != 0);
                auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &root_offsets_chunks_
                        [wp & (root_offsets_chunks_.size() - 1)]);
                p->store(o, std::memory_order_release);
                next_version_.store(next_wp, std::memory_order_release);
                if (o != INVALID_OFFSET) {
                    update_version_lower_bound_();
                }
            }

            void assign(size_t const i, chunk_offset_t const o) noexcept
            {
                auto *p = start_lifetime_as<std::atomic<chunk_offset_t>>(
                    &root_offsets_chunks_
                        [i & (root_offsets_chunks_.size() - 1)]);
                p->store(o, std::memory_order_release);
                update_version_lower_bound_(
                    (o != INVALID_OFFSET) ? i : uint64_t(-1));
            }

            chunk_offset_t operator[](size_t const i) const noexcept
            {
                return start_lifetime_as<std::atomic<chunk_offset_t> const>(
                           &root_offsets_chunks_
                               [i & (root_offsets_chunks_.size() - 1)])
                    ->load(std::memory_order_acquire);
            }

            // return INVALID_BLOCK_ID indicates that db is empty
            uint64_t max_version() const noexcept
            {
                auto const wp = next_version_.load(std::memory_order_acquire);
                return wp - 1;
            }

            void reset_all(uint64_t const version)
            {
                version_lower_bound_.store(0, std::memory_order_release);
                next_version_.store(0, std::memory_order_release);
                for (size_t i = 0; i < capacity(); ++i) {
                    push(INVALID_OFFSET);
                }
                version_lower_bound_.store(version, std::memory_order_release);
                next_version_.store(version, std::memory_order_release);
            }

            void rewind_to_version(uint64_t const version)
            {
                MONAD_ASSERT(version < max_version());
                MONAD_ASSERT(max_version() - version <= capacity());
                for (uint64_t i = version + 1; i <= max_version(); i++) {
                    assign(i, async::INVALID_OFFSET);
                }
                if (version <
                    version_lower_bound_.load(std::memory_order_acquire)) {
                    version_lower_bound_.store(
                        version, std::memory_order_release);
                }
                next_version_.store(version + 1, std::memory_order_release);
                update_version_lower_bound_();
            }
        };

        return root_offsets_delegator{&db_metadata_[which]};
    }

    // translate between virtual and physical addresses chunk_offset_t
    virtual_chunk_offset_t physical_to_virtual(chunk_offset_t) const noexcept;

    // age is relative to the beginning chunk's count
    std::pair<chunk_list, detail::unsigned_20>
    chunk_list_and_age(uint32_t idx) const noexcept;

    void append(chunk_list list, uint32_t idx) noexcept;
    void remove(uint32_t idx) noexcept;

    template <typename Func, typename... Args>
        requires std::invocable<
            std::function<void(detail::db_metadata *, Args...)>,
            detail::db_metadata *, Args...>
    void modify_metadata(Func func, Args &&...args) noexcept
    {
        func(db_metadata_[0].main, std::forward<Args>(args)...);
        func(db_metadata_[1].main, std::forward<Args>(args)...);
    }

    // This function should only be invoked after completing a upsert
    void advance_db_offsets_to(
        chunk_offset_t fast_offset, chunk_offset_t slow_offset) noexcept;

    void append_root_offset(chunk_offset_t root_offset) noexcept;
    void update_root_offset(size_t i, chunk_offset_t root_offset) noexcept;
    void fast_forward_next_version(uint64_t version) noexcept;

    void update_history_length_metadata(uint64_t history_len) noexcept;
    void set_latest_finalized_version(uint64_t) noexcept;
    void set_latest_verified_version(uint64_t) noexcept;
    uint64_t get_latest_finalized_version() const noexcept;
    uint64_t get_latest_verified_version() const noexcept;

    int64_t get_auto_expire_version_metadata() const noexcept;

    // WARNING: These are destructive, they discard immediately any extraneous
    // data.
    void rewind_to_match_offsets();
    void rewind_to_version(uint64_t version);

    void set_initial_insertion_count_unit_testing_only(uint32_t count)
    {
        initial_insertion_count_on_pool_creation_ = count;
    }

    // WARNING: for unit testing only
    // DO NOT invoke it outside of unit test
    void alternate_slow_fast_node_writer_unit_testing_only(bool alternate)
    {
        alternate_slow_fast_writer_ = alternate;
    }

    bool alternate_slow_fast_writer() const noexcept
    {
        return alternate_slow_fast_writer_;
    }

    bool can_write_to_fast() const noexcept
    {
        return can_write_to_fast_;
    }

    void set_can_write_to_fast(bool v) noexcept
    {
        can_write_to_fast_ = v;
    }

    constexpr bool is_in_memory() const noexcept
    {
        return io == nullptr;
    }

    constexpr bool is_on_disk() const noexcept
    {
        return io != nullptr;
    }

    double disk_usage() const
    {
        return 1.0 -
               (double)num_chunks(chunk_list::free) / (double)io->chunk_count();
    }

    chunk_offset_t get_latest_root_offset() const noexcept
    {
        MONAD_ASSERT(this->is_on_disk());
        auto const ro = root_offsets();
        return ro[ro.max_version()];
    }

    chunk_offset_t
    get_root_offset_at_version(uint64_t const version) const noexcept
    {
        MONAD_ASSERT(this->is_on_disk());
        if (version <= db_history_max_version()) {
            auto const offset = root_offsets()[version];
            if (version >= db_history_range_lower_bound()) {
                return offset;
            }
        }
        return INVALID_OFFSET;
    }

    bool version_is_valid_ondisk(uint64_t const version) const noexcept
    {
        MONAD_ASSERT(is_on_disk());
        return get_root_offset_at_version(version) != INVALID_OFFSET;
    }

    chunk_offset_t get_start_of_wip_fast_offset() const noexcept
    {
        MONAD_ASSERT(this->is_on_disk());
        return db_metadata()->db_offsets.start_of_wip_offset_fast;
    }

    chunk_offset_t get_start_of_wip_slow_offset() const noexcept
    {
        MONAD_ASSERT(this->is_on_disk());
        return db_metadata()->db_offsets.start_of_wip_offset_slow;
    }

    file_offset_t get_lower_bound_free_space() const noexcept
    {
        MONAD_ASSERT(this->is_on_disk());
        return db_metadata()->capacity_in_free_list;
    }

    uint32_t num_chunks(chunk_list const list) const noexcept;

    uint64_t version_history_max_possible() const noexcept;
    uint64_t version_history_length() const noexcept;

    // Following funcs on db history are for on disk db only. In
    // memory db does not have any version history.
    // Db history range, returned version NOT always valid
    uint64_t db_history_range_lower_bound() const noexcept;
    uint64_t db_history_max_version() const noexcept;
    // Returns the first min version with a root offset. On disk db returns
    // invalid if it contains empty version
    uint64_t db_history_min_valid_version() const noexcept;
};

static_assert(
    sizeof(UpdateAuxImpl) == 160 + sizeof(detail::TrieUpdateCollectedStats));
static_assert(alignof(UpdateAuxImpl) == 8);

template <lockable_or_void LockType = void>
class UpdateAux final : public UpdateAuxImpl
{
    mutable LockType lock_;

    virtual void lock_unique_() const override
    {
        MONAD_ASSERT(!is_current_thread_concurrent_to_upsert());
        lock_.lock();
    }

    virtual void unlock_unique_() const noexcept override
    {
        MONAD_ASSERT(!is_current_thread_concurrent_to_upsert());
        lock_.unlock();
    }

    virtual void lock_shared_() const override
    {
        if (!is_current_thread_upserting()) {
            MONAD_ASSERT(!is_current_thread_concurrent_to_upsert());
            if constexpr (requires(LockType x) { x.lock_shared(); }) {
                lock_.lock_shared();
            }
            else {
                lock_.lock();
            }
        }
    }

    virtual void unlock_shared_() const noexcept override
    {
        if (!is_current_thread_upserting()) {
            MONAD_ASSERT(!is_current_thread_concurrent_to_upsert());
            if constexpr (requires(LockType x) { x.unlock_shared(); }) {
                return lock_.unlock_shared();
            }
            else {
                return lock_.unlock();
            }
        }
    }

    virtual bool upgrade_shared_to_unique_() const noexcept override
    {
        MONAD_ASSERT(!is_current_thread_concurrent_to_upsert());
        if constexpr (requires(LockType x) {
                          x.try_unlock_shared_and_lock();
                          x.unlock_and_lock_shared();
                      }) {
            return lock_.try_unlock_shared_and_lock();
        }
        else {
            return false;
        }
    }

    virtual bool downgrade_unique_to_shared_() const noexcept override
    {
        MONAD_ASSERT(!is_current_thread_concurrent_to_upsert());
        if constexpr (requires(LockType x) {
                          x.try_unlock_shared_and_lock();
                          x.unlock_and_lock_shared();
                      }) {
            lock_.unlock_and_lock_shared();
            return true;
        }
        return false;
    }

public:
    UpdateAux(
        MONAD_ASYNC_NAMESPACE::AsyncIO *io_ = nullptr,
        std::optional<uint64_t> const history_len = {})
        : UpdateAuxImpl(io_, history_len)
    {
    }

    UpdateAux(
        LockType &&lock, MONAD_ASYNC_NAMESPACE::AsyncIO *io_ = nullptr,
        std::optional<uint64_t> const history_len = {})
        : UpdateAuxImpl(io_, history_len)
        , lock_(std::move(lock))
    {
    }

    ~UpdateAux()
    {
        // Prevent race on vptr
        std::atomic_thread_fence(std::memory_order_acq_rel);
    }

    LockType &lock() noexcept
    {
        return lock_;
    }
};

template <>
class UpdateAux<void> final : public UpdateAuxImpl
{

    virtual void lock_unique_() const override {}

    virtual void unlock_unique_() const noexcept override {}

    virtual void lock_shared_() const override {}

    virtual void unlock_shared_() const noexcept override {}

    virtual bool upgrade_shared_to_unique_() const noexcept override
    {
        return true;
    }

    virtual bool downgrade_unique_to_shared_() const noexcept override
    {
        return true;
    }

public:
    UpdateAux(
        MONAD_ASYNC_NAMESPACE::AsyncIO *io_ = nullptr,
        std::optional<uint64_t> const history_len = {})
        : UpdateAuxImpl(io_, history_len)
    {
    }

    ~UpdateAux()
    {
        // Prevent race on vptr
        std::atomic_thread_fence(std::memory_order_acq_rel);
    }
};

template <receiver Receiver>
    requires(
        MONAD_ASYNC_NAMESPACE::compatible_sender_receiver<
            read_short_update_sender, Receiver> &&
        MONAD_ASYNC_NAMESPACE::compatible_sender_receiver<
            read_long_update_sender, Receiver> &&
        Receiver::lifetime_managed_internally)
void async_read(UpdateAuxImpl &aux, Receiver &&receiver)
{
    [[likely]] if (
        receiver.bytes_to_read <=
        MONAD_ASYNC_NAMESPACE::AsyncIO::READ_BUFFER_SIZE) {
        read_short_update_sender sender(receiver);
        auto iostate =
            aux.io->make_connected(std::move(sender), std::move(receiver));
        iostate->initiate();
        // TEMPORARY UNTIL ALL THIS GETS BROKEN OUT: Release
        // management until i/o completes
        iostate.release();
    }
    else {
        read_long_update_sender sender(receiver);
        using connected_type =
            decltype(connect(*aux.io, std::move(sender), std::move(receiver)));
        auto *iostate = new connected_type(
            connect(*aux.io, std::move(sender), std::move(receiver)));
        iostate->initiate();
        // drop iostate
    }
}

// batch upsert, updates can be nested
Node::UniquePtr upsert(
    UpdateAuxImpl &, uint64_t, StateMachine &, Node::UniquePtr old,
    UpdateList &&);

// Performs a deep copy of a subtrie from `src_root` trie at
// `src_prefix` to the `dest_root` trie at `dest_prefix`.
// Note that `src_root` may be of a different version than `dest_root`.
// Any pre-existing trie at `dest_prefix` will be overwritten.
// The in-memory effect is similar to a move operation.
Node::UniquePtr copy_trie_to_dest(
    UpdateAuxImpl &, Node &src_root, NibblesView src_prefix,
    Node::UniquePtr dest_root, NibblesView dest_prefx,
    uint64_t const dest_version, bool must_write_to_disk);

// load all nodes as far as caching policy would allow
size_t load_all(UpdateAuxImpl &, StateMachine &, NodeCursor);

//////////////////////////////////////////////////////////////////////////////
// find

enum class find_result : uint8_t
{
    unknown,
    success,
    version_no_longer_exist,
    root_node_is_null_failure,
    key_mismatch_failure,
    branch_not_exist_failure,
    key_ends_earlier_than_node_failure,
    need_to_continue_in_io_thread
};
using find_result_type = std::pair<NodeCursor, find_result>;

using inflight_map_t = unordered_dense_map<
    chunk_offset_t,
    std::vector<std::function<MONAD_ASYNC_NAMESPACE::result<void>(NodeCursor)>>,
    chunk_offset_t_hasher>;

// The request type to put to the fiber buffered channel for triedb thread
// to work on
struct fiber_find_request_t
{
    threadsafe_boost_fibers_promise<find_result_type> *promise;
    NodeCursor start{};
    NibblesView key{};
};

static_assert(sizeof(fiber_find_request_t) == 40);
static_assert(alignof(fiber_find_request_t) == 8);
static_assert(std::is_trivially_copyable_v<fiber_find_request_t> == true);

//! \warning this is not threadsafe, should only be called from triedb thread
// during execution, DO NOT invoke it directly from a transaction fiber, as is
// not race free.
void find_notify_fiber_future(
    UpdateAuxImpl &, inflight_map_t &inflights, fiber_find_request_t);

/*! \brief blocking find node indexed by key from root, It works for both
on-disk and in-memory trie. When node along key is not yet in memory, it loads
the node through blocking read.

\warning Should only invoke it from the triedb owning
thread, as no synchronization is provided, and user code should make sure no
other place is modifying trie. */
find_result_type
find_blocking(UpdateAuxImpl const &, NodeCursor, NibblesView key);

//////////////////////////////////////////////////////////////////////////////
// helpers
inline constexpr unsigned num_pages(file_offset_t const offset, unsigned bytes)
{
    auto const rd_offset = round_down_align<DISK_PAGE_BITS>(offset);
    bytes += static_cast<unsigned>(offset - rd_offset);
    return (bytes + DISK_PAGE_SIZE - 1) >> DISK_PAGE_BITS;
}

inline std::pair<compact_virtual_chunk_offset_t, compact_virtual_chunk_offset_t>
calc_min_offsets(
    Node &node,
    virtual_chunk_offset_t node_virtual_offset = INVALID_VIRTUAL_OFFSET)
{
    auto fast_ret = INVALID_COMPACT_VIRTUAL_OFFSET;
    auto slow_ret = INVALID_COMPACT_VIRTUAL_OFFSET;
    if (node_virtual_offset != INVALID_VIRTUAL_OFFSET) {
        auto const truncated_offset =
            compact_virtual_chunk_offset_t{node_virtual_offset};
        if (node_virtual_offset.in_fast_list()) {
            fast_ret = truncated_offset;
        }
        else {
            slow_ret = truncated_offset;
        }
    }
    for (unsigned i = 0; i < node.number_of_children(); ++i) {
        fast_ret = std::min(fast_ret, node.min_offset_fast(i));
        slow_ret = std::min(slow_ret, node.min_offset_slow(i));
    }
    // if ret is valid
    if (fast_ret != INVALID_COMPACT_VIRTUAL_OFFSET) {
        MONAD_ASSERT(fast_ret < (1u << 31));
    }
    if (slow_ret != INVALID_COMPACT_VIRTUAL_OFFSET) {
        MONAD_ASSERT(slow_ret < (1u << 31));
    }
    return {fast_ret, slow_ret};
}

MONAD_MPT_NAMESPACE_END
