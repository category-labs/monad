#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/db/config.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/logging/monad_log.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/trie/in_memory_comparator.hpp>
#include <monad/trie/in_memory_cursor.hpp>
#include <monad/trie/in_memory_writer.hpp>
#include <monad/trie/key_buffer.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/node.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/rocks_cursor.hpp>
#include <monad/trie/rocks_writer.hpp>
#include <monad/trie/trie.hpp>

#include <boost/endian/conversion.hpp>
#include <ethash/keccak.hpp>
#include <fmt/chrono.h>
#include <fmt/format.h>
#include <rocksdb/db.h>

#include <bits/ranges_algo.h>
#include <filesystem>
#include <unordered_map>

MONAD_DB_NAMESPACE_BEGIN

namespace impl
{
    template <typename TDBImpl, typename TExecution>
    struct DBInterface
    {
        struct Updates
        {
            std::unordered_map<address_t, std::optional<Account>> accounts;
            std::unordered_map<
                address_t, std::unordered_map<bytes32_t, bytes32_t>>
                storage;
        } updates{};

        decltype(TExecution::get_executor()) executor{
            TExecution::get_executor()};

        TDBImpl &self() { return static_cast<TDBImpl &>(*this); }
        TDBImpl const &self() const
        {
            return static_cast<TDBImpl const &>(*this);
        }

        [[nodiscard]] std::optional<Account> try_find(address_t const &a)
        {
            return self().try_find(a);
        }

        [[nodiscard]] std::optional<Account> query(address_t const &a)
        {
            return executor([=, this]() { return try_find(a); });
        }

        [[nodiscard]] constexpr bool contains(address_t const &a)
        {
            return self().contains(a);
        }

        [[nodiscard]] constexpr bool
        contains(address_t const &a, bytes32_t const &k)
        {
            return self().contains(a, k);
        }

        [[nodiscard]] Account at(address_t const &a)
        {
            auto const ret = try_find(a);
            MONAD_ASSERT(ret);
            return ret.value();
        }

        [[nodiscard]] std::optional<bytes32_t>
        query(address_t const &a, bytes32_t const &k)
        {
            return executor([=, this]() { return try_find(a, k); });
        }

        [[nodiscard]] std::optional<bytes32_t>
        try_find(address_t const &a, bytes32_t const &k)
        {
            return self().try_find(a, k);
        }

        [[nodiscard]] bytes32_t at(address_t const &a, bytes32_t const &k)
        {
            auto const ret = try_find(a, k);
            MONAD_ASSERT(ret);
            return ret.value();
        }

        void create(address_t const &a, Account const &acct)
        {
            MONAD_DEBUG_ASSERT(!contains(a));
            auto const [_, inserted] = updates.accounts.try_emplace(a, acct);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void create(address_t const &a, bytes32_t const &k, bytes32_t const &v)
        {
            MONAD_DEBUG_ASSERT(v != bytes32_t{});
            MONAD_DEBUG_ASSERT(!contains(a, k));
            auto const [_, inserted] = updates.storage[a].try_emplace(k, v);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void update(address_t const &a, Account const &acct)
        {
            MONAD_DEBUG_ASSERT(contains(a));
            auto const [_, inserted] = updates.accounts.try_emplace(a, acct);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void update(address_t const &a, bytes32_t const &k, bytes32_t const &v)
        {
            MONAD_DEBUG_ASSERT(v != bytes32_t{});
            MONAD_DEBUG_ASSERT(contains(a));
            MONAD_DEBUG_ASSERT(contains(a, k));
            auto const [_, inserted] = updates.storage[a].try_emplace(k, v);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void erase(address_t const &a)
        {
            MONAD_DEBUG_ASSERT(contains(a));
            auto const [_, inserted] =
                updates.accounts.try_emplace(a, std::nullopt);
            MONAD_DEBUG_ASSERT(inserted);
        }

        void erase(address_t const &a, bytes32_t const &k)
        {
            MONAD_DEBUG_ASSERT(contains(a));
            MONAD_DEBUG_ASSERT(contains(a, k));
            auto const [_, inserted] =
                updates.storage[a].try_emplace(k, bytes32_t{});
            MONAD_DEBUG_ASSERT(inserted);
        }

        void commit_storage_impl() { self().commit_storage_impl(); }

        void commit_storage()
        {
            commit_storage_impl();
            updates.storage.clear();
        }

        void commit_accounts_impl() { self().commit_accounts_impl(); }

        void commit_accounts()
        {
            commit_accounts_impl();
            updates.accounts.clear();
        }

        void commit()
        {
            commit_storage();
            commit_accounts();
        }
    };

    template <typename TExecution>
    struct InMemoryDBImpl
        : public DBInterface<InMemoryDBImpl<TExecution>, TExecution>
    {
        using DBInterface<InMemoryDBImpl<TExecution>, TExecution>::updates;

        std::unordered_map<address_t, Account> accounts;
        std::unordered_map<address_t, std::unordered_map<bytes32_t, bytes32_t>>
            storage;

        [[nodiscard]] bool contains(address_t const &a) const
        {
            return accounts.contains(a);
        }

        [[nodiscard]] bool
        contains(address_t const &a, bytes32_t const &k) const
        {
            return storage.contains(a) && storage.at(a).contains(k);
        }

        [[nodiscard]] std::optional<Account> try_find(address_t const &a) const
        {
            if (accounts.contains(a)) {
                return accounts.at(a);
            }
            return std::nullopt;
        }

        [[nodiscard]] std::optional<bytes32_t>
        try_find(address_t const &a, bytes32_t const &k) const
        {
            if (!contains(a, k)) {
                return std::nullopt;
            }
            return storage.at(a).at(k);
        }

        void commit_storage_impl()
        {
            for (auto const &[a, updates] : updates.storage) {
                for (auto const &[k, v] : updates) {
                    if (v != bytes32_t{}) {
                        storage[a][k] = v;
                    }
                    else {
                        auto const n = storage[a].erase(k);
                        MONAD_DEBUG_ASSERT(n == 1);
                    }
                }
                if (storage[a].empty()) {
                    storage.erase(a);
                }
            }
        }

        void commit_accounts_impl()
        {
            for (auto const &[a, acct] : updates.accounts) {
                if (acct.has_value()) {
                    accounts[a] = acct.value();
                }
                else {
                    auto const n = accounts.erase(a);
                    MONAD_DEBUG_ASSERT(n == 1);
                }
            }
        }
    };

    constexpr auto
    make_basic_storage_key(address_t const &a, bytes32_t const &k)
    {
        byte_string_fixed<sizeof(address_t) + sizeof(bytes32_t)> key;
        std::copy_n(a.bytes, sizeof(address_t), key.data());
        std::copy_n(k.bytes, sizeof(bytes32_t), &key[sizeof(address_t)]);
        return key;
    }

    template <typename TExecution>
    struct RocksDBImpl : public DBInterface<RocksDBImpl<TExecution>, TExecution>
    {
        using DBInterface<RocksDBImpl<TExecution>, TExecution>::updates;

        std::filesystem::path const name;
        rocksdb::Options options;
        std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
        std::vector<rocksdb::ColumnFamilyHandle *> cfs;
        std::shared_ptr<rocksdb::DB> db;
        rocksdb::WriteBatch batch;

        RocksDBImpl(
            std::filesystem::path name = std::filesystem::absolute("db"))
            : name(name)
            , options([]() {
                rocksdb::Options ret;
                ret.IncreaseParallelism(2);
                ret.OptimizeLevelStyleCompaction();
                ret.create_if_missing = true;
                ret.create_missing_column_families = true;
                return ret;
            }())
            , cfds([&]() -> decltype(cfds) {
                return {
                    {rocksdb::kDefaultColumnFamilyName, {}},
                    {"PlainAccounts", {}},
                    {"PlainStorage", {}}};
            }())
            , cfs()
            , db([&]() {
                if (std::filesystem::exists(name)) {
                    MONAD_ASSERT(std::filesystem::is_directory(name));
                }
                else {
                    std::filesystem::create_directory(name);
                }

                rocksdb::DB *db = nullptr;

                rocksdb::Status const s = rocksdb::DB::Open(
                    options,
                    name / fmt::format("{}", std::chrono::system_clock::now()),
                    cfds,
                    &cfs,
                    &db);

                MONAD_ROCKS_ASSERT(s);
                MONAD_ASSERT(cfds.size() == cfs.size());

                return db;
            }())
            , batch()
        {
        }

        ~RocksDBImpl()
        {
            rocksdb::Status res;
            for (auto *const cf : cfs) {
                res = db->DestroyColumnFamilyHandle(cf);
                MONAD_ASSERT(res.ok());
            }

            res = db->Close();
            MONAD_ROCKS_ASSERT(res);
        }

        [[nodiscard]] constexpr rocksdb::ColumnFamilyHandle *accounts()
        {
            return cfs[1];
        }

        [[nodiscard]] constexpr rocksdb::ColumnFamilyHandle *storage()
        {
            return cfs[2];
        }

        [[nodiscard]] bool contains(address_t const &a)
        {
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, accounts(), to_slice(a), &value);
            MONAD_ASSERT(res.ok() || res.IsNotFound());
            return res.ok();
        }

        [[nodiscard]] bool contains(address_t const &a, bytes32_t const &k)
        {
            auto const key = make_basic_storage_key(a, k);
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, storage(), to_slice(key), &value);
            MONAD_ASSERT(res.ok() || res.IsNotFound());
            return res.ok();
        }

        [[nodiscard]] std::optional<Account> try_find(address_t const &a)
        {
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, accounts(), to_slice(a), &value);
            if (res.IsNotFound()) {
                return std::nullopt;
            }
            MONAD_ASSERT(res.ok());

            Account ret;
            bytes32_t _;
            auto const rest = rlp::decode_account(
                ret,
                _,
                {reinterpret_cast<byte_string_view::value_type const *>(
                     value.data()),
                 value.size()});
            MONAD_ASSERT(rest.empty());
            return ret;
        }

        [[nodiscard]] std::optional<bytes32_t>
        try_find(address_t const &a, bytes32_t const &k)
        {
            auto const key = make_basic_storage_key(a, k);
            rocksdb::PinnableSlice value;
            auto const res = db->Get(
                rocksdb::ReadOptions{}, storage(), to_slice(key), &value);
            if (res.IsNotFound()) {
                return std::nullopt;
            }
            MONAD_ROCKS_ASSERT(res);
            MONAD_ASSERT(value.size() == sizeof(bytes32_t));
            bytes32_t result;
            std::copy_n(value.data(), sizeof(bytes32_t), result.bytes);
            return result;
        }

        void commit_db()
        {
            rocksdb::WriteOptions options;
            options.disableWAL = true;
            db->Write(options, &batch);
            batch.Clear();
        }

        void commit_storage_impl()
        {
            for (auto const &[a, updates] : updates.storage) {
                for (auto const &[k, v] : updates) {
                    auto const key = make_basic_storage_key(a, k);
                    if (v != bytes32_t{}) {
                        auto const res =
                            batch.Put(storage(), to_slice(key), to_slice(v));
                        MONAD_ROCKS_ASSERT(res);
                    }
                    else {
                        auto const res = batch.Delete(storage(), to_slice(key));
                        MONAD_ROCKS_ASSERT(res);
                    }
                }
            }
            commit_db();
        }

        void commit_accounts_impl()
        {
            for (auto const &[a, acct] : updates.accounts) {
                if (acct.has_value()) {
                    // Note: no storage root calculations in this mode
                    auto const res = batch.Put(
                        accounts(),
                        to_slice(a),
                        to_slice(rlp::encode_account(acct.value(), NULL_ROOT)));
                    MONAD_ROCKS_ASSERT(res);
                }
                else {
                    auto const res = batch.Delete(accounts(), to_slice(a));
                    MONAD_ROCKS_ASSERT(res);
                }
            }
            commit_db();
        }
    };

    struct InMemoryTrieSetup
    {
        template <typename TComparator>
        struct Trie
        {
            using cursor_t = trie::InMemoryCursor<TComparator>;
            using writer_t = trie::InMemoryWriter<TComparator>;
            using storage_t = typename cursor_t::storage_t;
            storage_t leaves_storage;
            cursor_t leaves_cursor;
            writer_t leaves_writer;
            storage_t trie_storage;
            cursor_t trie_cursor;
            writer_t trie_writer;
            trie::Trie<cursor_t, writer_t> trie;

            Trie()
                : leaves_storage{}
                , leaves_cursor{leaves_storage}
                , leaves_writer{leaves_storage}
                , trie_storage{}
                , trie_cursor{trie_storage}
                , trie_writer{trie_storage}
                , trie{leaves_cursor, trie_cursor, leaves_writer, trie_writer}
            {
            }
        };

        Trie<trie::InMemoryPathComparator> accounts;
        Trie<trie::InMemoryPrefixPathComparator> storage;

        InMemoryTrieSetup(std::filesystem::path)
            : accounts{}
            , storage{}
        {
        }

        void take_snapshot() {}
        void release_snapshot() {}
    };

    struct RocksDBTrieSetup
    {
        struct Trie
        {
            trie::RocksCursor leaves_cursor;
            trie::RocksCursor trie_cursor;
            trie::RocksWriter leaves_writer;
            trie::RocksWriter trie_writer;

            trie::Trie<trie::RocksCursor, trie::RocksWriter> trie;

            Trie(
                std::shared_ptr<rocksdb::DB> db,
                rocksdb::ColumnFamilyHandle *lc,
                rocksdb::ColumnFamilyHandle *tc,
                rocksdb::Snapshot const *snapshot)
                : leaves_cursor(db, lc, snapshot)
                , trie_cursor(db, tc, snapshot)
                , leaves_writer(trie::RocksWriter{
                      .db = db, .batch = rocksdb::WriteBatch{}, .cf = lc})
                , trie_writer(trie::RocksWriter{
                      .db = db, .batch = rocksdb::WriteBatch{}, .cf = tc})
                , trie(leaves_cursor, trie_cursor, leaves_writer, trie_writer)
            {
            }

            void set_snapshot(rocksdb::Snapshot const *snapshot)
            {
                leaves_cursor.set_snapshot(snapshot);
                trie_cursor.set_snapshot(snapshot);
            }

            void reset_cursor()
            {
                leaves_cursor.reset();
                trie_cursor.reset();
            }
        };

        std::filesystem::path const name;
        rocksdb::Options options;
        trie::PathComparator accounts_comparator;
        trie::PrefixPathComparator storage_comparator;
        std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
        std::vector<rocksdb::ColumnFamilyHandle *> cfs;
        std::shared_ptr<rocksdb::DB> db;
        rocksdb::Snapshot const *snapshot;
        Trie accounts;
        Trie storage;

        RocksDBTrieSetup(std::filesystem::path name)
            : name(name)
            , options([]() {
                rocksdb::Options ret;
                ret.IncreaseParallelism(2);
                ret.OptimizeLevelStyleCompaction();
                ret.create_if_missing = true;
                ret.create_missing_column_families = true;
                return ret;
            }())
            , accounts_comparator()
            , storage_comparator()
            , cfds([&]() -> decltype(cfds) {
                rocksdb::ColumnFamilyOptions accounts_opts;
                rocksdb::ColumnFamilyOptions storage_opts;
                accounts_opts.comparator = &accounts_comparator;
                storage_opts.comparator = &storage_comparator;

                return {
                    {rocksdb::kDefaultColumnFamilyName, {}},
                    {"AccountTrieLeaves", accounts_opts},
                    {"AccountTrieAll", accounts_opts},
                    {"StorageTrieLeaves", storage_opts},
                    {"StorageTrieAll", storage_opts}};
            }())
            , cfs()
            , db([&]() {
                if (std::filesystem::exists(name)) {
                    MONAD_ASSERT(std::filesystem::is_directory(name));
                }
                else {
                    std::filesystem::create_directory(name);
                }

                rocksdb::DB *db = nullptr;

                rocksdb::Status const s = rocksdb::DB::Open(
                    options,
                    name / fmt::format("{}", std::chrono::system_clock::now()),
                    cfds,
                    &cfs,
                    &db);

                MONAD_ROCKS_ASSERT(s);
                MONAD_ASSERT(cfds.size() == cfs.size());

                return db;
            }())
            , snapshot(db->GetSnapshot())
            , accounts(db, cfs[1], cfs[2], snapshot)
            , storage(db, cfs[3], cfs[4], snapshot)
        {
        }

        void take_snapshot()
        {
            release_snapshot();
            snapshot = db->GetSnapshot();
            accounts.set_snapshot(snapshot);
            storage.set_snapshot(snapshot);
        }

        void release_snapshot()
        {
            MONAD_DEBUG_ASSERT(snapshot);
            db->ReleaseSnapshot(snapshot);
        }

        ~RocksDBTrieSetup()
        {
            accounts.reset_cursor();
            storage.reset_cursor();
            release_snapshot();

            rocksdb::Status res;
            for (auto *const cf : cfs) {
                res = db->DestroyColumnFamilyHandle(cf);
                MONAD_ASSERT(res.ok());
            }

            res = db->Close();
            MONAD_ROCKS_ASSERT(res);
        }
    };

    template <typename TTrie>
    [[nodiscard]] constexpr auto make_leaf_cursor(TTrie const &trie)
    {
        if constexpr (std::same_as<TTrie, RocksDBTrieSetup::Trie>) {
            return trie::RocksCursor{
                trie.leaves_cursor.db_,
                trie.leaves_cursor.cf_,
                trie.leaves_cursor.read_opts_.snapshot};
        }
        else {
            return decltype(trie.leaves_cursor){trie.leaves_storage};
        }
    };

    template <typename TTrie>
    [[nodiscard]] constexpr auto make_trie_cursor(TTrie const &trie)
    {
        if constexpr (std::same_as<TTrie, RocksDBTrieSetup::Trie>) {
            return trie::RocksCursor{
                trie.trie_cursor.db_,
                trie.trie_cursor.cf_,
                trie.trie_cursor.read_opts_.snapshot};
        }
        else {
            return decltype(trie.trie_cursor){trie.trie_storage};
        }
    };

    template <typename TTrieSetup, typename TExecutor>
    struct TrieDBImpl
        : public DBInterface<TrieDBImpl<TTrieSetup, TExecutor>, TExecutor>
    {
        using DBInterface<
            TrieDBImpl<TTrieSetup, TExecutor>, TExecutor>::updates;

        TTrieSetup setup;
        decltype(TTrieSetup::accounts) &accounts;
        decltype(TTrieSetup::storage) &storage;
        std::vector<trie::Update> account_trie_updates;
        std::vector<trie::Update> storage_trie_updates;

        TrieDBImpl(
            std::filesystem::path name = std::filesystem::absolute("trie_db"))
            : setup{name}
            , accounts{setup.accounts}
            , storage{setup.storage}
            , account_trie_updates{}
            , storage_trie_updates{}
        {
        }

        decltype(monad::log::logger_t::get_logger()) logger =
            monad::log::logger_t::get_logger("trie_db_logger");
        static_assert(std::is_pointer_v<decltype(logger)>);

        [[nodiscard]] constexpr bytes32_t root_hash() const
        {
            return accounts.trie.root_hash();
        }

        [[nodiscard]] constexpr bytes32_t root_hash(address_t a)
        {
            storage.trie.set_trie_prefix(a);
            return storage.trie.root_hash();
        }

        template <typename TCursor>
        [[nodiscard]] constexpr bool
        move(trie::Nibbles const &lk, TCursor &lc, TCursor &tc) const
        {
            lc.lower_bound(lk);

            if (lc.key().transform(&TCursor::Key::path) != lk) {
                return false;
            }

            lc.prev();

            auto const left =
                lc.key()
                    .transform(&TCursor::Key::path)
                    .transform([&](auto const &l) {
                        return trie::longest_common_prefix_size(l, lk);
                    });

            lc.next();
            MONAD_DEBUG_ASSERT(lc.key().transform(&TCursor::Key::path) == lk);
            lc.next();

            auto const right =
                lc.key()
                    .transform(&TCursor::Key::path)
                    .transform([&](auto const &r) {
                        return trie::longest_common_prefix_size(lk, r);
                    });

            auto const tk =
                !left.has_value() && !right.has_value()
                    ? trie::Nibbles{}
                    : trie::Nibbles{lk.prefix(static_cast<uint8_t>(
                          std::max(left.value_or(0), right.value_or(0)) + 1))};

            tc.lower_bound(tk);
            return tc.key().transform(&TCursor::Key::path) == tk;
        }

        // TODO: make this return the keccak so that it can be just passed in
        // to avoid double keccaking?
        [[nodiscard]] constexpr tl::optional<
            decltype(make_trie_cursor(accounts))>
        find(address_t const &a) const
        {
            auto lc = make_leaf_cursor(accounts);
            auto tc = make_trie_cursor(accounts);
            auto const found = move(
                trie::Nibbles{std::bit_cast<bytes32_t>(
                    ethash::keccak256(a.bytes, sizeof(a.bytes)))},
                lc,
                tc);

            if (found) {
                return tc;
            }
            return tl::nullopt;
        }

        [[nodiscard]] constexpr tl::optional<
            decltype(make_trie_cursor(storage))>
        find(address_t const &a, bytes32_t const &k) const
        {
            auto lc = make_leaf_cursor(storage);
            auto tc = make_trie_cursor(storage);

            lc.set_prefix(a);
            tc.set_prefix(a);

            auto const found = move(
                trie::Nibbles{std::bit_cast<bytes32_t>(
                    ethash::keccak256(k.bytes, sizeof(k.bytes)))},
                lc,
                tc);

            if (found) {
                return tc;
            }
            return tl::nullopt;
        }

        [[nodiscard]] constexpr bool contains(address_t const &a) const
        {
            return find(a).has_value();
        }

        [[nodiscard]] constexpr bool
        contains(address_t const &a, bytes32_t const &k) const
        {
            return find(a, k).has_value();
        }

        [[nodiscard]] std::optional<Account> try_find(address_t const &a) const
        {
            auto const c = find(a);
            if (!c.has_value()) {
                return std::nullopt;
            }

            auto const key =
                c->key().transform(&decltype(c)::value_type::Key::path);
            MONAD_ASSERT(key.has_value());

            auto const value = c->value();
            MONAD_ASSERT(value.has_value());

            auto const node = trie::deserialize_node(*key, *value);
            MONAD_ASSERT(std::holds_alternative<trie::Leaf>(node));

            Account ret;
            bytes32_t _;
            auto const rest =
                rlp::decode_account(ret, _, std::get<trie::Leaf>(node).value);
            MONAD_ASSERT(rest.empty());
            return ret;
        }

        [[nodiscard]] std::optional<bytes32_t>
        try_find(address_t const &a, bytes32_t const &k) const
        {
            auto const c = find(a, k);
            if (!c.has_value()) {
                return std::nullopt;
            }

            auto const key =
                c->key().transform(&decltype(c)::value_type::Key::path);
            MONAD_ASSERT(key.has_value());

            auto const value = c->value();
            MONAD_ASSERT(c.has_value());

            auto const node = trie::deserialize_node(*key, *value);
            MONAD_ASSERT(std::holds_alternative<trie::Leaf>(node));

            byte_string zeroless;
            auto const rest =
                rlp::decode_string(zeroless, std::get<trie::Leaf>(node).value);
            MONAD_ASSERT(rest.empty());
            MONAD_ASSERT(zeroless.size() <= sizeof(bytes32_t));

            bytes32_t ret;
            std::copy_n(
                zeroless.data(),
                zeroless.size(),
                std::next(
                    std::begin(ret.bytes),
                    static_cast<uint8_t>(sizeof(bytes32_t) - zeroless.size())));
            MONAD_ASSERT(ret != bytes32_t{});
            return ret;
        }

        void commit_storage_impl()
        {
            if (updates.storage.empty()) {
                return;
            }

            for (auto const &u : updates.storage) {
                MONAD_DEBUG_ASSERT(!u.second.empty());

                storage.trie.set_trie_prefix(u.first);

                storage_trie_updates.clear();
                std::ranges::transform(
                    u.second,
                    std::back_inserter(storage_trie_updates),
                    [](auto const &su) -> trie::Update {
                        auto const &[k, v] = su;
                        auto const key = trie::Nibbles{std::bit_cast<bytes32_t>(
                            ethash::keccak256(k.bytes, sizeof(k.bytes)))};
                        auto const value = rlp::encode_string(
                            zeroless_view(to_byte_string_view(v.bytes)));
                        if (v != bytes32_t{}) {
                            return trie::Upsert{.key = key, .value = value};
                        }
                        return trie::Delete{.key = key};
                    });

                std::ranges::sort(
                    storage_trie_updates, std::less<>{}, trie::get_update_key);

                MONAD_LOG_INFO(
                    logger,
                    "{} storage updates for {}: {}",
                    storage_trie_updates.size(),
                    u.first,
                    storage_trie_updates);
                storage.trie.process_updates(storage_trie_updates);
            }
            storage.leaves_writer.write();
            storage.trie_writer.write();
            setup.take_snapshot();
        }

        void commit_accounts_impl()
        {
            MONAD_DEBUG_ASSERT(updates.storage.empty());

            if (updates.accounts.empty()) {
                return;
            }

            for (auto const &u : updates.accounts) {
                auto const &[a, acct] = u;
                storage.trie.set_trie_prefix(a);
                auto const ak = trie::Nibbles{std::bit_cast<bytes32_t>(
                    ethash::keccak256(a.bytes, sizeof(a.bytes)))};
                if (acct.has_value()) {
                    account_trie_updates.emplace_back(trie::Upsert{
                        .key = ak,
                        .value = rlp::encode_account(
                            acct.value(), storage.trie.root_hash())});
                }
                else {
                    storage.trie.clear();
                    account_trie_updates.emplace_back(trie::Delete{.key = ak});
                }
            }

            std::ranges::sort(
                account_trie_updates, std::less<>{}, trie::get_update_key);
            MONAD_LOG_INFO(
                logger,
                "{} account updates: {}",
                account_trie_updates.size(),
                account_trie_updates);
            accounts.trie.process_updates(account_trie_updates);

            accounts.leaves_writer.write();
            accounts.trie_writer.write();
            storage.leaves_writer.write();
            storage.trie_writer.write();
            setup.take_snapshot();
            account_trie_updates.clear();
        }
    };
}

// Database impl with trie root generating logic, backed by stl
using InMemoryTrieDB = impl::TrieDBImpl<
    impl::InMemoryTrieSetup, monad::execution::BoostFiberExecution>;

// Database impl with trie root generating logic, backed by rocksdb
using RocksTrieDB = impl::TrieDBImpl<
    impl::RocksDBTrieSetup, monad::execution::BoostFiberExecution>;

// Database impl without trie root generating logic, backed by stl
using InMemoryDB = impl::InMemoryDBImpl<monad::execution::BoostFiberExecution>;

// Database impl without trie root generating logic, backed by rocksdb
using RocksDB = impl::RocksDBImpl<monad::execution::BoostFiberExecution>;

MONAD_DB_NAMESPACE_END
