#include "triedb.h"

#include <atomic>
#include <cassert>
#include <exception>
#include <filesystem>
#include <limits>
#include <mutex>
#include <stdexcept>
#include <vector>

#include <monad/async/concepts.hpp>
#include <monad/config.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/nibble.h>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/traverse_util.hpp>

#include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#include <boost/outcome/experimental/status-code/status-code/status_code.hpp>
#include <boost/outcome/experimental/status-code/status-code/status_code_domain.hpp>
#include <boost/outcome/experimental/status-code/status-code/system_code.hpp>

#define EXPORT_DECL __attribute__((visibility("default")))
#define EXTERN_C extern "C" EXPORT_DECL

enum class monad_c_triedb_errc : uint8_t
{
    unknown = 0,
    value_too_big,
    invalid_block_id,
    exception_not_matched
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad_c_triedb_errc>
    : quick_status_code_from_enum_defaults<monad_c_triedb_errc>
{
    static constexpr auto const domain_name = "monad_c_triedb_errc domain";

    static constexpr auto const domain_uuid =
        "{1d1f77e3-c5b9-ca8e-b909-e2da6ef843fe}";

    static std::initializer_list<mapping> const &value_mappings()
    {
        static std::initializer_list<mapping> const v = {
            {monad_c_triedb_errc::value_too_big,
             "value too big",
             {errc::no_buffer_space}},
            {monad_c_triedb_errc::invalid_block_id,
             "invalid block id",
             {errc::argument_out_of_domain}},
            {monad_c_triedb_errc::exception_not_matched,
             "exception not matched",
             {}},
            {monad_c_triedb_errc::unknown, "unknown", {}},
        };
        return v;
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

static struct custom_cxx_exception_strings_t
{
    class my_atomic_refcounted_string_ref;
    friend class my_atomic_refcounted_string_ref;

    mutable std::mutex lock;

    struct slot_t
    {
        std::string msg;
        mutable std::atomic<unsigned> count;
    };

    std::array<slot_t, 256> slots;
    size_t slot_idx{0};

    size_t push(std::string const &msg)
    {
        std::lock_guard g(lock);
        auto myidx = slot_idx++;
        while (slots[myidx % slots.size()].count.load(
                   std::memory_order_relaxed) > 0) {
            myidx = slot_idx++;
        }
        slots[myidx % slots.size()].msg = msg;
        return myidx;
    }

    slot_t *get(size_t idx)
    {
        std::lock_guard g(lock);
        if (slot_idx - idx >= slots.size()) {
            return nullptr;
        }
        return &slots[idx % slots.size()];
    }

    BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain::string_ref
    get_string_ref(size_t idx) const;
} custom_cxx_exception_strings;

/*! A reference counted, threadsafe reference to a message string.
 */
class custom_cxx_exception_strings_t::my_atomic_refcounted_string_ref
    : public BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain::
          string_ref
{
    // Returns all bits set for an empty string ref
    size_t _slot_idx() const noexcept
    {
        return (size_t)(uintptr_t)(this->_state[0]) - 1;
    }

    static BOOST_OUTCOME_SYSTEM_ERROR2_CONSTEXPR20 void
    _refcounted_string_thunk(
        string_ref *_dest, string_ref const *_src, _thunk_op op) noexcept
    {
        auto *dest = static_cast<my_atomic_refcounted_string_ref *>(_dest);
        auto const *src =
            static_cast<my_atomic_refcounted_string_ref const *>(_src);
        (void)src;
        assert(dest->_thunk == _refcounted_string_thunk);
        assert(src == nullptr || src->_thunk == _refcounted_string_thunk);
        switch (op) {
        case _thunk_op::copy: {
            if (dest->_slot_idx() != (size_t)-1) {
                auto const *slot =
                    custom_cxx_exception_strings.get(dest->_slot_idx());
                assert(slot != nullptr);
                auto count =
                    slot->count.fetch_add(1, std::memory_order_relaxed);
                (void)count;
                assert(count != 0);
            }
            return;
        }
        case _thunk_op::move: {
            assert(src);
            auto *msrc = const_cast<my_atomic_refcounted_string_ref *>(src);
            msrc->_begin = msrc->_end = nullptr;
            msrc->_state[0] = msrc->_state[1] = msrc->_state[2] = nullptr;
            return;
        }
        case _thunk_op::destruct: {
            if (dest->_slot_idx() != (size_t)-1) {
                auto *slot =
                    custom_cxx_exception_strings.get(dest->_slot_idx());
                assert(slot != nullptr);
                auto count =
                    slot->count.fetch_sub(1, std::memory_order_release);
                if (count == 1) {
                    slot->msg = "";
                }
            }
        }
        }
    }

public:
    my_atomic_refcounted_string_ref(
        size_t const idx, slot_t const &slot) noexcept
        : string_ref(
              slot.msg.c_str(), slot.msg.size(), (void *)(uintptr_t)(idx + 1),
              nullptr, nullptr, _refcounted_string_thunk)
    {
        slot.count.fetch_add(1, std::memory_order_relaxed);
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain::string_ref
custom_cxx_exception_strings_t::get_string_ref(size_t idx) const
{
    std::lock_guard g(lock);
    if (slot_idx - idx >= slots.size()) {
        return BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain::
            string_ref("unknown C++ exception text due to slot expiring");
    }
    return my_atomic_refcounted_string_ref(idx, slots[idx % slots.size()]);
}

class custom_cxx_exception_domain_;
using custom_cxx_exception_code =
    BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<
        custom_cxx_exception_domain_>;

class custom_cxx_exception_domain_
    : public BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain
{
    using base_ = BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain;

public:
    using value_type = size_t;

    constexpr explicit custom_cxx_exception_domain_(
        base_::unique_id_type id = 0x0feb3d1f164b195a) noexcept
        : base_(id)
    {
    }

    static inline constexpr custom_cxx_exception_domain_ const &get();

    virtual base_::string_ref name() const noexcept override final
    {
        static string_ref v("custom C++ exception error domain");
        return v;
    }

    constexpr virtual payload_info_t
    payload_info() const noexcept override final
    {
        return {
            sizeof(value_type),
            sizeof(custom_cxx_exception_code),
            alignof(custom_cxx_exception_code)};
    }

    constexpr virtual bool _do_failure(
        BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> const &)
        const noexcept override final
    {
        return true;
    }

    constexpr virtual bool _do_equivalent(
        BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> const &,
        BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> const &)
        const noexcept override final
    {
        return false;
    }

    constexpr virtual BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::generic_code
    _generic_code(BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> const
                      &) const noexcept override final
    {
        return BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::errc::unknown;
    }

    virtual base_::string_ref _do_message(
        BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> const &code)
        const noexcept override final
    {
        assert(code.domain() == *this);
        return custom_cxx_exception_strings.get_string_ref(
            static_cast<const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
                            status_code<custom_cxx_exception_domain_> &>(code)
                .value());
    }

    virtual void _do_throw_exception(
        BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> const &code)
        const override final
    {
        assert(code.domain() == *this);
        throw std::runtime_error(
            custom_cxx_exception_strings
                .get_string_ref(
                    static_cast<
                        const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
                            status_code<custom_cxx_exception_domain_> &>(code)
                        .value())
                .c_str());
    }
};

constexpr custom_cxx_exception_domain_ custom_cxx_exception_domain;

inline constexpr custom_cxx_exception_domain_ const &
custom_cxx_exception_domain_::get()
{
    return custom_cxx_exception_domain;
}

static inline monad_c_result make_c_result(monad_c_triedb_errc v)
{
    auto sc =
        BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::quick_status_code_from_enum_code<
            monad_c_triedb_errc>(v);
    return to_system_monad(std::move(sc));
}

static inline monad_c_result
make_c_result(BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::system_code sc)
{
    return to_system_monad(std::move(sc));
}

static inline monad_c_result
make_c_result(std::exception_ptr ep = std::current_exception())
{
    BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::system_code not_matched(
        monad_c_triedb_errc::exception_not_matched);
    // Try to map to a standard error code first
    auto ep2 = ep;
    auto sc =
        BOOST_OUTCOME_V2_NAMESPACE::experimental::system_code_from_exception(
            std::move(ep2), monad_c_triedb_errc::exception_not_matched);
    if (sc.domain() != not_matched.domain()) {
        if (sc.domain() !=
                BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::generic_code_domain ||
            sc.value() != EAGAIN) {
            return to_system_monad(std::move(sc));
        }
    }
    // Otherwise try to extract the error string
    try {
        std::rethrow_exception(std::move(ep));
    }
    catch (std::exception const &e) {
        return to_system_monad(custom_cxx_exception_code(
            custom_cxx_exception_strings.push(e.what())));
    }
    catch (...) {
        std::cerr << "WARNING: make_c_result() returns EAGAIN as exception "
                     "throw type is unknown."
                  << std::endl;
        return to_system_monad(std::move(not_matched));
    }
}

struct monad_c_triedb
{
    explicit monad_c_triedb(std::vector<std::filesystem::path> dbname_paths)
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

EXTERN_C monad_c_result
monad_c_triedb_open(char const *dbpaths[], monad_c_triedb **db)
{
    try {
        if (*db != nullptr) {
            return monad_c_make_failure(EINVAL);
        }

        std::vector<std::filesystem::path> paths;
        for (char const **dbdirpath = dbpaths; *dbdirpath != nullptr;
             dbdirpath++) {
            paths.emplace_back(*dbdirpath);
        }

        *db = new monad_c_triedb{std::move(paths)};
        return monad_c_make_success(0);
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result monad_c_triedb_close(monad_c_triedb *db)
{
    try {
        delete db;
        return monad_c_make_success(0);
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result monad_c_triedb_read(
    monad_c_triedb *db, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    monad_c_triedb_bytes *value, uint64_t block_id)
{
    try {
        auto result = db->db_.get(
            monad::mpt::NibblesView{0, key_len_nibbles, key}, block_id);
        if (!result.has_value()) {
            return make_c_result(std::move(result).assume_error());
        }

        auto const &value_view = result.value();
        if ((value_view.size() >> std::numeric_limits<int>::digits) != 0) {
            // value length doesn't fit in return type
            return make_c_result(monad_c_triedb_errc::value_too_big);
        }
        *value = new uint8_t[value_view.size()];
        memcpy((void *)*value, value_view.data(), value_view.size());
        return monad_c_make_success((intptr_t)value_view.size());
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C void monad_c_triedb_async_read(
    monad_c_triedb *db, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    uint64_t block_id,
    void (*completed)(monad_c_result value, size_t length, void *user),
    void *user)
{
    try {
        struct receiver_t
        {
            void (*completed_)(monad_c_result value, size_t length, void *user);
            void *user_;

            void set_value(
                monad::async::erased_connected_operation *state,
                monad::async::result<monad::byte_string> result)
            {
                monad_c_result value;
                size_t length = 0;
                auto completed = completed_;
                auto *user = user_;
                if (!result) {
                    value = make_c_result(std::move(result).assume_error());
                    length = (size_t)-1;
                }
                else {
                    auto const &value_view = result.value();
                    if ((value_view.size() >>
                         std::numeric_limits<int>::digits) != 0) {
                        // value length doesn't fit in return type
                        value =
                            make_c_result(monad_c_triedb_errc::value_too_big);
                        length = (size_t)-1;
                    }
                    else {
                        auto *p = new uint8_t[value_view.size()];
                        memcpy(p, value_view.data(), value_view.size());
                        value = monad_c_make_success((intptr_t)p);
                        length = value_view.size();
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
    catch (...) {
        completed(make_c_result(), 0, user);
    }
}

namespace detail
{
    static monad_c_result const success_kind_callback_value =
        monad_c_make_success(triedb_async_traverse_callback_value);
    static monad_c_result const success_kind_callback_finished_normally =
        monad_c_make_success(triedb_async_traverse_callback_finished_normally);
    static monad_c_result const success_kind_callback_finished_early =
        monad_c_make_success(triedb_async_traverse_callback_finished_early);

    class Traverse final : public monad::mpt::TraverseMachine
    {
        void *context_;
        monad_c_triedb_callback_func callback_;
        monad::mpt::Nibbles path_;

    public:
        Traverse(
            void *context, monad_c_triedb_callback_func callback,
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
                    success_kind_callback_value,
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
        monad_c_triedb_callback_func callback;

        void set_value(
            monad::async::erased_connected_operation *state,
            monad::async::result<bool> res)
        {
            MONAD_ASSERT_PRINTF(
                res,
                "triedb_async_traverse: Traversing failed with %s",
                res.assume_error().message().c_str());
            callback(
                res.assume_value() ? success_kind_callback_finished_normally
                                   : success_kind_callback_finished_early,
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
            void *context, monad_c_triedb_callback_func callback,
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
                    success_kind_callback_finished_normally,
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

EXTERN_C bool monad_c_triedb_traverse(
    monad_c_triedb *db, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    uint64_t block_id, void *context, monad_c_triedb_callback_func callback)
{
    try {
        auto prefix = monad::mpt::NibblesView{0, key_len_nibbles, key};
        auto cursor = db->db_.find(prefix, block_id);
        if (!cursor.has_value()) {
            callback(
                make_c_result(std::move(cursor).assume_error()),
                context,
                nullptr,
                0,
                nullptr,
                0);
            return false;
        }

        detail::Traverse machine(context, callback, monad::mpt::NibblesView{});

        bool const completed =
            db->db_.traverse(cursor.value(), machine, block_id);

        callback(
            completed ? detail::success_kind_callback_finished_normally
                      : detail::success_kind_callback_finished_early,
            context,
            nullptr,
            0,
            nullptr,
            0);
        return completed;
    }
    catch (...) {
        callback(make_c_result(), context, nullptr, 0, nullptr, 0);
        return false;
    }
}

EXTERN_C void monad_c_triedb_async_traverse(
    monad_c_triedb *db, monad_c_triedb_bytes key, uint8_t key_len_nibbles,
    uint64_t block_id, void *context, monad_c_triedb_callback_func callback)
{
    try {
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
    catch (...) {
        callback(make_c_result(), context, nullptr, 0, nullptr, 0);
    }
}

EXTERN_C void monad_c_triedb_async_ranged_get(
    monad_c_triedb *db, monad_c_triedb_bytes prefix_key,
    uint8_t prefix_len_nibbles, monad_c_triedb_bytes min_key,
    uint8_t min_len_nibbles, monad_c_triedb_bytes max_key,
    uint8_t max_len_nibbles, uint64_t block_id, void *context,
    monad_c_triedb_callback_func callback)
{
    try {
        monad::mpt::NibblesView const prefix{0, prefix_len_nibbles, prefix_key};
        monad::mpt::NibblesView const min{0, min_len_nibbles, min_key};
        monad::mpt::NibblesView const max{0, max_len_nibbles, max_key};
        auto machine = std::make_unique<monad::mpt::RangedGetMachine>(
            min,
            max,
            [callback, context](
                monad::mpt::NibblesView const key,
                monad::byte_string_view value) {
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
                    detail::success_kind_callback_value,
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
    catch (...) {
        callback(make_c_result(), context, nullptr, 0, nullptr, 0);
    }
}

EXTERN_C monad_c_result
monad_c_triedb_poll(monad_c_triedb *db, bool blocking, size_t count)
{
    try {
        return monad_c_make_success((intptr_t)db->db_.poll(blocking, count));
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result monad_c_triedb_finalize(monad_c_triedb_bytes value)
{
    try {
        delete[] value;
        return monad_c_make_success(0);
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result monad_c_triedb_latest_voted_block(monad_c_triedb *db)
{
    try {
        uint64_t latest_voted_block_id = db->db_.get_latest_voted_block_id();

        if (latest_voted_block_id != monad::mpt::INVALID_BLOCK_ID) {
            return monad_c_make_success((intptr_t)latest_voted_block_id);
        }
        else {
            // no block has been produced
            return make_c_result(monad_c_triedb_errc::invalid_block_id);
        }
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result monad_c_triedb_latest_voted_round(monad_c_triedb *db)
{
    try {
        uint64_t latest_round = db->db_.get_latest_voted_round();

        if (latest_round != monad::mpt::INVALID_BLOCK_ID) {
            return monad_c_make_success((intptr_t)latest_round);
        }
        else {
            // no block has been produced
            return make_c_result(monad_c_triedb_errc::invalid_block_id);
        }
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result
monad_c_triedb_latest_finalized_block(monad_c_triedb *db)
{
    try {
        uint64_t latest_block_id = db->db_.get_latest_finalized_block_id();

        if (latest_block_id != monad::mpt::INVALID_BLOCK_ID) {
            return monad_c_make_success((intptr_t)latest_block_id);
        }
        else {
            // no block has been produced
            return make_c_result(monad_c_triedb_errc::invalid_block_id);
        }
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result monad_c_triedb_latest_verified_block(monad_c_triedb *db)
{
    try {
        uint64_t latest_block_id = db->db_.get_latest_verified_block_id();

        if (latest_block_id != monad::mpt::INVALID_BLOCK_ID) {
            return monad_c_make_success((intptr_t)latest_block_id);
        }
        else {
            // no block has been produced
            return make_c_result(monad_c_triedb_errc::invalid_block_id);
        }
    }
    catch (...) {
        return make_c_result();
    }
}

EXTERN_C monad_c_result
monad_c_triedb_earliest_finalized_block(monad_c_triedb *db)
{
    try {
        uint64_t earliest_block_id = db->db_.get_earliest_block_id();

        if (earliest_block_id != monad::mpt::INVALID_BLOCK_ID) {
            return monad_c_make_success((intptr_t)earliest_block_id);
        }
        else {
            // no block has been produced
            return make_c_result(monad_c_triedb_errc::invalid_block_id);
        }
    }
    catch (...) {
        return make_c_result();
    }
}
