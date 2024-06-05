#include <monad/mpt/db.hpp>

#include <monad/async/config.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/io.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/db_error.hpp>
#include <monad/mpt/detail/boost_fiber_workarounds.hpp>
#include <monad/mpt/find_request_sender.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <boost/container/deque.hpp>
#include <boost/fiber/operations.hpp>

#include <atomic>
#include <cerrno>
#include <chrono>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <iterator>
#include <memory>
#include <mutex>
#include <optional>
#include <system_error>
#include <thread>
#include <utility>
#include <variant>
#include <vector>

#include <fcntl.h>
#include <linux/fs.h>
#include <unistd.h>

#undef BLOCK_SIZE // without this concurrentqueue.h gets sad
#include "concurrentqueue.h"

MONAD_MPT_NAMESPACE_BEGIN

struct Db::Impl
{
    bool upsert_running_{false};
    bool prefetch_running_{false};

    virtual ~Impl() = default;

    virtual Node::UniquePtr &root() = 0;
    virtual UpdateAux<> &aux() = 0;
    virtual void upsert_fiber_blocking(
        UpdateList &&, uint64_t, bool enable_compaction,
        bool can_write_to_fast) = 0;

    virtual find_result_type find_fiber_blocking(
        NodeCursor const &root, NibblesView const &key, uint64_t version) = 0;
    virtual bool is_latest() const = 0;
    virtual void load_latest_fiber_blocking() = 0;
    virtual size_t prefetch_fiber_blocking(uint64_t latest_block_id) = 0;
};

struct Db::ROOnDisk final : public Db::Impl
{
    async::storage_pool pool_;
    io::Ring ring_;
    io::Buffers rwbuf_;
    async::AsyncIO io_;
    UpdateAux<> aux_;
    uint64_t last_loaded_max_version_;
    chunk_offset_t last_loaded_offset_;
    Node::UniquePtr root_;

    ROOnDisk(ReadOnlyOnDiskDbConfig const &options)
        : pool_{[&] -> async::storage_pool {
            async::storage_pool::creation_flags pool_options;
            pool_options.open_read_only = true;
            pool_options.disable_mismatching_storage_pool_check =
                options.disable_mismatching_storage_pool_check;
            MONAD_ASSERT(!options.dbname_paths.empty());
            return async::storage_pool{
                options.dbname_paths,
                async::storage_pool::mode::open_existing,
                pool_options};
        }()}
        , ring_{monad::io::RingConfig{
              options.uring_entries, false, options.sq_thread_cpu}}
        , rwbuf_{io::make_buffers_for_read_only(
              ring_, options.rd_buffers,
              async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE)}
        , io_{pool_, rwbuf_}
        , aux_{&io_}
        , last_loaded_max_version_{aux_.db_metadata()
                                       ->max_db_history_version.load(
                                           std::memory_order_acquire)}
        , last_loaded_offset_{[&] {
            auto root_offset = aux_.get_root_offset();
            if (root_offset == INVALID_OFFSET) {
                throw std::runtime_error("Failed to open a read-only db from "
                                         "an empty database.");
            }
            return root_offset;
        }()}
        , root_{Node::UniquePtr{read_node_blocking(pool_, last_loaded_offset_)}}
    {
        io_.set_capture_io_latencies(options.capture_io_latencies);
        io_.set_concurrent_read_io_limit(options.concurrent_read_io_limit);
        io_.set_eager_completions(options.eager_completions);
    }

    ~ROOnDisk()
    {
        aux_.unique_lock();
        // must be destroyed before aux is destroyed
        aux_.unset_io();
    }

    virtual Node::UniquePtr &root() override
    {
        return root_;
    }

    virtual UpdateAux<> &aux() override
    {
        return aux_;
    }

    virtual void
    upsert_fiber_blocking(UpdateList &&, uint64_t, bool, bool) override
    {
        MONAD_ASSERT(false);
    }

    virtual find_result_type find_fiber_blocking(
        NodeCursor const &root, NibblesView const &key,
        uint64_t const version) override
    {
        // db we last loaded does not contain the version we want to find
        if (version > last_loaded_max_version_ ||
            version < aux().db_metadata()->min_db_history_version.load(
                          std::memory_order_acquire)) {
            return {NodeCursor{}, find_result::unknown};
        }
        try {

            auto const res = find_blocking(aux(), root, key);
            // verify version still valid in history after success
            return version >= aux().db_metadata()->min_db_history_version.load(
                                  std::memory_order_acquire)
                       ? res
                       : find_result_type{NodeCursor{}, find_result::unknown};
        }
        catch (std::exception const &e) { // exception implies UB
            return {NodeCursor{}, find_result::unknown};
        }
    }

    virtual bool is_latest() const override
    {
        return last_loaded_offset_ == aux_.get_root_offset();
    }

    virtual void load_latest_fiber_blocking() override
    {
        if (last_loaded_offset_ == aux_.get_root_offset()) {
            return;
        }
        // Do not change the order of loading max version and root offset
        // max version can be smaller than the current root actually has but
        // can't be greater.
        last_loaded_max_version_ =
            aux_.db_metadata()->max_db_history_version.load(
                std::memory_order_acquire);
        last_loaded_offset_ = aux_.get_root_offset();
        root_.reset(read_node_blocking(pool_, last_loaded_offset_));
    }

    virtual size_t prefetch_fiber_blocking(uint64_t) override
    {
        MONAD_ASSERT(false);
    }
};

struct Db::InMemory final : public Db::Impl
{
    UpdateAux<> aux_;
    StateMachine &machine_;
    Node::UniquePtr root_;

    explicit InMemory(StateMachine &machine)
        : aux_{nullptr}
        , machine_{machine}
    {
    }

    virtual Node::UniquePtr &root() override
    {
        return root_;
    }

    virtual UpdateAux<> &aux() override
    {
        return aux_;
    }

    virtual void upsert_fiber_blocking(
        UpdateList &&list, uint64_t block_id, bool, bool) override
    {
        root_ = aux_.do_update(
            std::move(root_), machine_, std::move(list), block_id, false);
    }

    virtual find_result_type find_fiber_blocking(
        NodeCursor const &root, NibblesView const &key, uint64_t = 0) override
    {
        return find_blocking(aux(), root, key);
    }

    virtual bool is_latest() const override
    {
        return true;
    }

    virtual void load_latest_fiber_blocking() override {}

    virtual size_t prefetch_fiber_blocking(uint64_t) override
    {
        return 0;
    }
};

struct Db::RWOnDisk final : public Db::Impl
{
    struct FiberUpsertRequest
    {
        threadsafe_boost_fibers_promise<Node::UniquePtr> *promise;
        Node::UniquePtr prev_root;
        StateMachine &sm;
        UpdateList &&updates;
        uint64_t const version;
        bool const enable_compaction;
        bool const can_write_to_fast;
    };

    struct FiberLoadAllFromBlockRequest
    {
        threadsafe_boost_fibers_promise<size_t> *promise;
        NodeCursor root;
        StateMachine &sm;
    };

    using Comms = std::variant<
        std::monostate, fiber_find_request_t, FiberUpsertRequest,
        FiberLoadAllFromBlockRequest>;
    ::moodycamel::ConcurrentQueue<Comms> comms_;

    std::mutex lock_;
    std::condition_variable cond_;

    struct TrieDbWorker
    {
        RWOnDisk *parent;
        UpdateAuxImpl &aux;

        async::storage_pool pool;
        io::Ring ring1, ring2;
        io::Buffers rwbuf;
        async::AsyncIO io;
        bool const compaction;
        std::atomic<bool> sleeping{false}, done{false};

        TrieDbWorker(
            RWOnDisk *parent, UpdateAuxImpl &aux, OnDiskDbConfig const &options)
            : parent(parent)
            , aux(aux)
            , pool{[&] -> async::storage_pool {
                if (options.dbname_paths.empty()) {
                    return async::storage_pool{
                        async::use_anonymous_inode_tag{}};
                }
                // initialize db file on disk
                for (auto const &dbname_path : options.dbname_paths) {
                    if (!std::filesystem::exists(dbname_path)) {
                        int const fd = ::open(
                            dbname_path.c_str(),
                            O_CREAT | O_RDWR | O_CLOEXEC,
                            0600);
                        if (-1 == fd) {
                            throw std::system_error(
                                errno, std::system_category());
                        }
                        auto unfd = monad::make_scope_exit(
                            [fd]() noexcept { ::close(fd); });
                        if (-1 ==
                            ::ftruncate(
                                fd,
                                options.file_size_db * 1024 * 1024 * 1024 +
                                    24576)) {
                            throw std::system_error(
                                errno, std::system_category());
                        }
                    }
                }
                return async::storage_pool{
                    options.dbname_paths,
                    options.append ? async::storage_pool::mode::open_existing
                                   : async::storage_pool::mode::truncate};
            }()}
            , ring1{{options.uring_entries, options.enable_io_polling, options.sq_thread_cpu}}
            , ring2{options.wr_buffers}
            , rwbuf{io::make_buffers_for_segregated_read_write(
                  ring1, ring2, options.rd_buffers, options.wr_buffers,
                  async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                  async::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE)}
            , io{pool, rwbuf}
            , compaction{options.compaction}
        {
            io.set_capture_io_latencies(options.capture_io_latencies);
            io.set_concurrent_read_io_limit(options.concurrent_read_io_limit);
            io.set_eager_completions(options.eager_completions);
        }

        // Runs in the triedb worker thread
        void run()
        {
            inflight_map_t inflights;
            ::boost::container::deque<
                threadsafe_boost_fibers_promise<find_result_type>>
                find_promises;
            ::boost::container::deque<
                threadsafe_boost_fibers_promise<Node::UniquePtr>>
                upsert_promises;
            ::boost::container::deque<threadsafe_boost_fibers_promise<size_t>>
                prefetch_promises;
            /* In case you're wondering why we use a vector for a single
            element, it's because for some odd reason the MoodyCamel concurrent
            queue only supports move only types via its iterator interface. No
            that makes no sense to me either, but it is what it is.
            */
            std::vector<Comms> request;
            request.reserve(1);
            unsigned did_nothing_count = 0;
            while (!done.load(std::memory_order_acquire)) {
                bool did_nothing = true;
                request.clear();
                if (parent->comms_.try_dequeue_bulk(
                        std::back_inserter(request), 1) > 0) {
                    if (auto *req = std::get_if<1>(&request.front());
                        req != nullptr) {
                        // The promise needs to hang around until its future is
                        // destructed, otherwise there is a race within
                        // Boost.Fiber. So we move the promise out of the
                        // submitting thread into a local deque which gets
                        // emptied when its future gets destroyed.
                        find_promises.emplace_back(std::move(*req->promise));
                        req->promise = &find_promises.back();
                        find_notify_fiber_future(aux, inflights, *req);
                    }
                    else if (auto *req = std::get_if<2>(&request.front());
                             req != nullptr) {
                        // Ditto to above
                        upsert_promises.emplace_back(std::move(*req->promise));
                        req->promise = &upsert_promises.back();
                        req->promise->set_value(aux.do_update(
                            std::move(req->prev_root),
                            req->sm,
                            std::move(req->updates),
                            req->version,
                            compaction && req->enable_compaction,
                            req->can_write_to_fast));
                    }
                    else if (auto *req = std::get_if<3>(&request.front());
                             req != nullptr) {
                        // Ditto to above
                        prefetch_promises.emplace_back(
                            std::move(*req->promise));
                        req->promise = &prefetch_promises.back();
                        req->promise->set_value(
                            mpt::load_all(aux, req->sm, req->root));
                    }
                    did_nothing = false;
                }
                io.poll_nonblocking(1);
                boost::this_fiber::yield();
                if (boost::fibers::has_ready_fibers()) {
                    did_nothing = false;
                }
                if (did_nothing && io.io_in_flight() > 0) {
                    did_nothing = false;
                }
                while (!find_promises.empty() &&
                       find_promises.front().future_has_been_destroyed()) {
                    find_promises.pop_front();
                }
                while (!upsert_promises.empty() &&
                       upsert_promises.front().future_has_been_destroyed()) {
                    upsert_promises.pop_front();
                }
                if (!find_promises.empty() || !upsert_promises.empty()) {
                    did_nothing = false;
                }
                if (did_nothing) {
                    did_nothing_count++;
                }
                else {
                    did_nothing_count = 0;
                }
                if (did_nothing_count > 1000000) {
                    std::unique_lock g(parent->lock_);
                    sleeping.store(true, std::memory_order_release);
                    /* Very irritatingly, Boost.Fiber may have fibers scheduled
                     which weren't ready before, and if we sleep forever here
                     then they never run and cause anything waiting on them to
                     hang. So pulse Boost.Fiber every second at most for those
                     extremely rare occasions.
                     */
                    parent->cond_.wait_for(g, std::chrono::seconds(1), [this] {
                        return done.load(std::memory_order_acquire) ||
                               parent->comms_.size_approx() > 0;
                    });
                    sleeping.store(false, std::memory_order_release);
                }
            }
        }
    };

    std::unique_ptr<TrieDbWorker> worker_;
    std::thread worker_thread_;
    StateMachine &machine_;
    UpdateAux<> aux_;
    Node::UniquePtr root_;

    RWOnDisk(OnDiskDbConfig const &options, StateMachine &machine)
        : worker_thread_([&] {
            {
                std::unique_lock const g(lock_);
                worker_ = std::make_unique<TrieDbWorker>(this, aux_, options);
            }
            worker_->run();
            std::unique_lock const g(lock_);
            worker_.reset();
        })
        , machine_{machine}
        , aux_{[&] {
            comms_.enqueue({});
            while (comms_.size_approx() > 0) {
                std::this_thread::yield();
            }
            std::unique_lock const g(lock_);
            MONAD_ASSERT(worker_);
            return UpdateAux<>{&worker_->io};
        }()}
        , root_(
              aux_.get_root_offset() != INVALID_OFFSET
                  ? Node::UniquePtr{read_node_blocking(
                        worker_->pool, aux_.get_root_offset())}
                  : Node::UniquePtr{})
    {
    }

    ~RWOnDisk()
    {
        aux_.unique_lock();
        // must be destroyed before aux is destroyed
        aux_.unset_io();
        {
            std::unique_lock const g(lock_);
            worker_->done.store(true, std::memory_order_release);
            cond_.notify_one();
        }
        worker_thread_.join();
    }

    virtual Node::UniquePtr &root() override
    {
        return root_;
    }

    virtual UpdateAux<> &aux() override
    {
        return aux_;
    }

    // threadsafe
    virtual find_result_type find_fiber_blocking(
        NodeCursor const &start, NibblesView const &key, uint64_t = 0) override
    {
        threadsafe_boost_fibers_promise<find_result_type> promise;
        fiber_find_request_t req{
            .promise = &promise, .start = start, .key = key};
        auto fut = promise.get_future();
        comms_.enqueue(req);
        // promise is racily emptied after this point
        if (worker_->sleeping.load(std::memory_order_acquire)) {
            std::unique_lock const g(lock_);
            cond_.notify_one();
        }
        return fut.get();
    }

    // threadsafe
    virtual void upsert_fiber_blocking(
        UpdateList &&updates, uint64_t const version,
        bool const enable_compaction, bool const can_write_to_fast) override
    {
        threadsafe_boost_fibers_promise<Node::UniquePtr> promise;
        auto fut = promise.get_future();
        comms_.enqueue(FiberUpsertRequest{
            .promise = &promise,
            .prev_root = std::move(root_),
            .sm = machine_,
            .updates = std::move(updates),
            .version = version,
            .enable_compaction = enable_compaction,
            .can_write_to_fast = can_write_to_fast});
        // promise is racily emptied after this point
        if (worker_->sleeping.load(std::memory_order_acquire)) {
            std::unique_lock const g(lock_);
            cond_.notify_one();
        }
        root_ = fut.get();
    }

    virtual bool is_latest() const override
    {
        return true;
    }

    virtual void load_latest_fiber_blocking() override {}

    // threadsafe
    virtual size_t prefetch_fiber_blocking(uint64_t latest_block_id) override
    {
        auto const block_id_prefix =
            serialize_as_big_endian<BLOCK_NUM_BYTES>(latest_block_id);
        NibblesView const block_nv{block_id_prefix};
        auto res = find_fiber_blocking(*root(), block_nv);
        for (uint8_t n = 0; n < block_nv.nibble_size(); ++n) {
            machine_.down(block_nv.get(n));
        }
        threadsafe_boost_fibers_promise<size_t> promise;
        auto fut = promise.get_future();
        comms_.enqueue(FiberLoadAllFromBlockRequest{
            .promise = &promise, .root = res.first, .sm = machine_});
        // promise is racily emptied after this point
        if (worker_->sleeping.load(std::memory_order_acquire)) {
            std::unique_lock const g(lock_);
            cond_.notify_one();
        }
        size_t const nodes_loaded = fut.get();
        machine_.up(block_nv.nibble_size());
        return nodes_loaded;
    }
};

Db::Db(StateMachine &machine)
    : impl_{std::make_unique<InMemory>(machine)}
{
}

Db::Db(StateMachine &machine, OnDiskDbConfig const &config)
    : impl_{std::make_unique<RWOnDisk>(config, machine)}
{
    MONAD_DEBUG_ASSERT(impl_->aux().is_on_disk());
}

Db::Db(ReadOnlyOnDiskDbConfig const &config)
    : impl_{std::make_unique<ROOnDisk>(config)}
{
}

Db::~Db() = default;

Result<NodeCursor>
Db::get(NodeCursor root, NibblesView const key, uint64_t const block_id) const
{
    MONAD_ASSERT(impl_);
    auto const [it, result] = impl_->find_fiber_blocking(root, key, block_id);
    if (result != find_result::success) {
        return DbError::key_not_found;
    }
    MONAD_DEBUG_ASSERT(it.node != nullptr);
    MONAD_DEBUG_ASSERT(it.node->has_value());
    return it;
}

Result<byte_string_view>
Db::get(NibblesView const key, uint64_t const block_id) const
{
    auto res = get(
        root(), serialize_as_big_endian<BLOCK_NUM_BYTES>(block_id), block_id);
    if (!res.has_value()) {
        return DbError::key_not_found;
    }
    res = get(res.value(), key, block_id);
    if (!res.has_value()) {
        return DbError::key_not_found;
    }
    return res.value().node->value();
}

Result<byte_string_view> Db::get_data(
    NodeCursor root, NibblesView const key, uint64_t const block_id) const
{
    auto res = get(root, key, block_id);
    if (!res.has_value()) {
        return DbError::key_not_found;
    }
    MONAD_DEBUG_ASSERT(res.value().node != nullptr);

    return res.value().node->data();
}

Result<byte_string_view>
Db::get_data(NibblesView const key, uint64_t const block_id) const
{
    auto res = get(
        root(), serialize_as_big_endian<BLOCK_NUM_BYTES>(block_id), block_id);
    if (!res.has_value()) {
        return DbError::key_not_found;
    }
    return get_data(res.value(), key, block_id);
}

void Db::upsert(
    UpdateList list, uint64_t const block_id, bool const enable_compaction,
    bool const can_write_to_fast)
{
    MONAD_ASSERT(impl_);
    MONAD_ASSERT(!impl_->upsert_running_);
    impl_->upsert_running_ = true;
    impl_->upsert_fiber_blocking(
        std::move(list), block_id, enable_compaction, can_write_to_fast);
    impl_->upsert_running_ = false;
}

void Db::traverse(
    NibblesView const prefix, TraverseMachine &machine, uint64_t const block_id)
{
    auto const block_id_prefix =
        serialize_as_big_endian<BLOCK_NUM_BYTES>(block_id);
    auto res = get(root(), NibblesView{block_id_prefix}, block_id);
    MONAD_ASSERT(res.has_value());
    res = get(res.value(), prefix, block_id);
    if (!res.has_value()) {
        return;
    }
    auto *node = res.value().node;
    MONAD_DEBUG_ASSERT(node != nullptr);
    preorder_traverse(impl_->aux(), *node, machine);
}

NodeCursor Db::root() const noexcept
{
    return impl_->root() ? NodeCursor{*impl_->root()} : NodeCursor{};
}

std::optional<uint64_t> Db::get_latest_block_id() const
{
    return impl_->root()
               ? std::make_optional<uint64_t>(
                     impl_->aux().max_version_in_db_history(*impl_->root()))
               : std::nullopt;
}

std::optional<uint64_t> Db::get_earliest_block_id() const
{
    return impl_->root()
               ? std::make_optional<uint64_t>(
                     impl_->aux().min_version_in_db_history(*impl_->root()))
               : std::nullopt;
}

bool Db::is_latest() const
{
    MONAD_ASSERT(impl_);
    return impl_->is_latest();
}

void Db::load_latest()
{
    MONAD_ASSERT(impl_);
    impl_->load_latest_fiber_blocking();
}

size_t Db::prefetch()
{
    MONAD_ASSERT(impl_);
    MONAD_ASSERT(!impl_->prefetch_running_);
    auto const latest_block_id = get_latest_block_id();
    if (!latest_block_id.has_value()) {
        return 0;
    }
    impl_->prefetch_running_ = true;
    size_t const nodes_loaded =
        impl_->prefetch_fiber_blocking(latest_block_id.value());
    impl_->prefetch_running_ = false;
    return nodes_loaded;
}

MONAD_MPT_NAMESPACE_END
