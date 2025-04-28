#include <ankerl/unordered_dense.h>
#include <cstdint>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/state2/state_deltas.hpp>
#include <monad/types/incarnation.hpp>

struct monad_statesync_client
{
    std::deque<monad_sync_request> rqs;
    uint64_t mask;
};

struct monad_statesync_server_network
{
    monad_statesync_client *client;
    monad_statesync_client_context *cctx;
    monad::byte_string buf;
};

MONAD_NAMESPACE_BEGIN

namespace test_statesync
{
    void statesync_send_request(
        monad_statesync_client *const client, monad_sync_request const rq)
    {
        client->rqs.push_back(rq);
    }

    ssize_t statesync_server_recv(
        monad_statesync_server_network *const net, unsigned char *const buf,
        size_t const len)
    {
        if (len == 1) {
            constexpr auto MSG_TYPE = SYNC_TYPE_REQUEST;
            std::memcpy(buf, &MSG_TYPE, 1);
        }
        else {
            MONAD_ASSERT(len == sizeof(monad_sync_request));
            std::memcpy(
                buf, &net->client->rqs.front(), sizeof(monad_sync_request));
            net->client->rqs.pop_front();
        }
        return static_cast<ssize_t>(len);
    }

    void statesync_server_send_upsert(
        monad_statesync_server_network *const net, monad_sync_type const type,
        unsigned char const *const v1, uint64_t const size1,
        unsigned char const *const v2, uint64_t const size2)
    {
        net->buf.clear();
        if (v1 != nullptr) {
            net->buf.append(v1, size1);
        }
        if (v2 != nullptr) {
            net->buf.append(v2, size2);
        }
        MONAD_ASSERT(monad_statesync_client_handle_upsert(
            net->cctx, 0, type, net->buf.data(), net->buf.size()));
    }

    void statesync_server_send_done(
        monad_statesync_server_network *const net, monad_sync_done const done)
    {
        monad_statesync_client_handle_done(net->cctx, done);
    }

    struct Range
    {
        uint64_t begin{0};
        uint64_t end{0};
    };

    struct State : Range
    {
        ankerl::unordered_dense::segmented_map<uint64_t, Range> storage;
    };

    void new_account(
        StateDeltas &deltas, State &state, Incarnation const incarnation,
        uint64_t const n)
    {
        bool const success = deltas.emplace(
            Address{state.end},
            StateDelta{
                .account = AccountDelta{
                    std::nullopt,
                    Account{.balance = n, .incarnation = incarnation}}});
        MONAD_ASSERT(success);
        ++state.end;
    }

    void update_account(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n,
        Incarnation const incarnation)
    {
        if (state.begin == state.end) {
            return;
        }
        uint64_t const addr = (n % (state.end - state.begin)) + state.begin;
        auto const orig = db.read_account(Address{addr});
        MONAD_ASSERT(orig.has_value());
        bool const reincarnate = (n % 10) == 1;
        // possible to generate duplicate key updates
        if (deltas.emplace(
                Address{addr},
                StateDelta{
                    .account = AccountDelta{
                        orig,
                        Account{
                            .balance = n,
                            .incarnation = reincarnate
                                               ? incarnation
                                               : orig.value().incarnation}}})) {
            if (reincarnate) {
                state.storage.erase(addr);
            }
        }
    }

    void remove_account(StateDeltas &deltas, State &state, TrieDb &db)
    {
        if (state.begin == state.end) {
            return;
        }
        Address const addr{state.begin};
        bool const success = deltas.emplace(
            addr,
            StateDelta{
                .account = AccountDelta{
                    db.read_account(Address{state.begin}), std::nullopt}});
        MONAD_ASSERT(success);
        state.storage.erase(state.begin);
        ++state.begin;
    }

    void
    new_storage(StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n)
    {
        if (state.begin == state.end) {
            return;
        }
        uint64_t const addr = n % (state.end - state.begin) + state.begin;
        auto const orig = db.read_account(Address{addr});
        MONAD_ASSERT(orig.has_value());
        StateDeltas::accessor it;
        bytes32_t const end{state.storage[addr].end++};
        if (!deltas.emplace(
                it,
                Address{addr},
                StateDelta{
                    .account = {orig, orig},
                    .storage =
                        StorageDeltas{{end, {bytes32_t{}, bytes32_t{n}}}}})) {
            bool success = it->second.storage.emplace(
                end, StorageDelta{bytes32_t{}, bytes32_t{n}});
            MONAD_ASSERT(success);
        }
    }

    void update_storage(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n,
        bool const erase)
    {
        if (state.storage.empty()) {
            return;
        }
        auto const sit = state.storage.begin() +
                         static_cast<unsigned>(n % state.storage.size());
        Address const addr{sit->first};
        auto const orig = db.read_account(addr);
        MONAD_ASSERT(orig.has_value());
        auto &[begin, end] = sit->second;
        MONAD_ASSERT(begin != end);
        bytes32_t const key{erase ? begin : n % (end - begin) + begin};
        bytes32_t const value{erase ? 0 : n};
        auto const sorig = db.read_storage(addr, orig->incarnation, key);
        MONAD_ASSERT(sorig != bytes32_t{});
        StateDeltas::accessor it;

        if (!deltas.emplace(
                it,
                addr,
                StateDelta{
                    .account = {orig, orig},
                    .storage = StorageDeltas{{key, {sorig, value}}}})) {
            // possible to generate duplicate key updates
            (void)it->second.storage.emplace(key, StorageDelta{sorig, value});
        }
        if (erase) {
            ++begin;
            if (begin == end) {
                state.storage.erase(sit);
            }
        }
    }

    void update_storage(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n)
    {
        update_storage(deltas, state, db, n, false);
    }

    void remove_storage(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n)
    {
        update_storage(deltas, state, db, n, true);
    }

    std::filesystem::path tmp_dbname()
    {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_fuzz_statesync_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        char const *const path = dbname.c_str();
        OnDiskMachine machine;
        mpt::Db const db{
            machine,
            mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
        return dbname;
    }

}

MONAD_NAMESPACE_END
