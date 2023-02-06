#include <monad/db/state_db.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>

#include <rocksdb/db.h>
#include <rocksdb/iterator.h>
#include <rocksdb/options.h>
#include <rocksdb/slice.h>
#include <rocksdb/status.h>
#include <rocksdb/write_batch.h>

#include <boost/endian/conversion.hpp>
#include <boost/log/trivial.hpp>

#include <cstring>

MONAD_NAMESPACE_BEGIN

static inline rocksdb::Slice to_slice(byte_string const &s)
{
    return rocksdb::Slice{reinterpret_cast<char const *>(s.data()), s.size()};
}

template <size_t N>
static inline rocksdb::Slice to_slice(byte_string_fixed<N> const &s)
{
    return rocksdb::Slice{reinterpret_cast<char const *>(s.data()), s.size()};
}

static inline rocksdb::Slice to_slice(address_t const &address)
{
    return rocksdb::Slice{reinterpret_cast<char const *>(address.bytes), 20};
}

static inline rocksdb::Slice to_slice(bytes32_t const &s)
{
    return rocksdb::Slice{reinterpret_cast<char const *>(s.bytes), 32};
}

static inline byte_string_view to_view(rocksdb::Slice const &s)
{
    return byte_string_view{
        reinterpret_cast<unsigned char const *>(s.data()), s.size()};
}

StateDb::StateDb(std::filesystem::path const &path)
    : path_{path}
    , cfs_{}
    , db_{[this] {
        rocksdb::Options options;
        options.IncreaseParallelism(2);
        options.OptimizeLevelStyleCompaction();

        std::vector<rocksdb::ColumnFamilyDescriptor> cfds;
        cfds.emplace_back(
            rocksdb::kDefaultColumnFamilyName, rocksdb::ColumnFamilyOptions{});
        cfds.emplace_back("PlainAccount", rocksdb::ColumnFamilyOptions{});
        cfds.emplace_back("PlainStorage", rocksdb::ColumnFamilyOptions{});
        cfds.emplace_back("HashedAccount", rocksdb::ColumnFamilyOptions{});
        cfds.emplace_back("HashedStorage", rocksdb::ColumnFamilyOptions{});
        cfds.emplace_back("AccountHistory", rocksdb::ColumnFamilyOptions{});
        cfds.emplace_back("StorageHistory", rocksdb::ColumnFamilyOptions{});

        rocksdb::DB *db = nullptr;
        if (std::filesystem::exists(path_ / "CURRENT")) {
            rocksdb::Status const s =
                rocksdb::DB::Open(options, path_.string(), cfds, &cfs_, &db);
            if (!s.ok()) {
                BOOST_LOG_TRIVIAL(error) << s.ToString();
            }
            MONAD_ASSERT(s.ok());
            MONAD_ASSERT(db);
        }
        else {
            options.create_if_missing = true;
            rocksdb::Status s = rocksdb::DB::Open(options, path_.string(), &db);
            if (!s.ok()) {
                BOOST_LOG_TRIVIAL(error) << s.ToString();
            }
            MONAD_ASSERT(s.ok());
            MONAD_ASSERT(db);
            cfs_.emplace_back(db->DefaultColumnFamily());
            for (auto const &cfd : cfds) {
                if (cfd.name == rocksdb::kDefaultColumnFamilyName) {
                    continue;
                }
                rocksdb::ColumnFamilyHandle *cf = nullptr;
                s = db->CreateColumnFamily(cfd.options, cfd.name, &cf);
                if (!s.ok()) {
                    BOOST_LOG_TRIVIAL(error) << s.ToString();
                }
                MONAD_ASSERT(s.ok());
                MONAD_ASSERT(cf);
                cfs_.emplace_back(cf);
            }
        }
        return db;
    }()}
    , batch_{new rocksdb::WriteBatch{}}
{
}

StateDb::~StateDb()
{
    for (auto *const cf : cfs_) {
        if (cf == db_->DefaultColumnFamily()) {
            continue;
        }
        db_->DestroyColumnFamilyHandle(cf);
    }
    cfs_.clear();
}

std::optional<Account> StateDb::read_account(address_t const &address)
{
    (void)address;
    (void)to_view;
    return {};
}

std::optional<Account> StateDb::read_account_history(
    address_t const &address, uint64_t const block_number)
{
    (void)address;
    (void)block_number;
    typedef rocksdb::Slice (*to_slice_t)(address_t const &);
    (void)(to_slice_t)to_slice;
    return {};
}

bytes32_t StateDb::read_storage(
    address_t const &address, uint64_t const incarnation,
    bytes32_t const &location)
{
    byte_string_fixed<60> key;
    std::memcpy(&key[0], address.bytes, 20);
    boost::endian::store_big_u64(&key[20], incarnation);
    std::memcpy(&key[28], location.bytes, 32);

    rocksdb::PinnableSlice value;
    auto const status =
        db_->Get(rocksdb::ReadOptions{}, cfs_[2], to_slice(key), &value);
    if (status.IsNotFound()) {
        return {};
    }
    MONAD_ASSERT(status.ok());
    MONAD_ASSERT(value.size() == 32);
    bytes32_t result;
    std::memcpy(result.bytes, value.data(), 32);
    return result;
}

bytes32_t StateDb::read_storage_history(
    address_t const &address, uint64_t const incarnation,
    bytes32_t const &location, uint64_t const block_number)
{
    byte_string_fixed<68> key;
    std::memcpy(&key[0], address.bytes, 20);
    boost::endian::store_big_u64(&key[20], incarnation);
    std::memcpy(&key[28], location.bytes, 32);
    boost::endian::store_big_u64(&key[60], block_number);

    std::unique_ptr<rocksdb::Iterator> const it{
        db_->NewIterator(rocksdb::ReadOptions{}, cfs_[6])};
    it->SeekForPrev(to_slice(key));
    if (!it->Valid()) {
        return {};
    }
    auto const it_key = it->key();
    MONAD_ASSERT(it_key.size() == 68);
    if (std::memcmp(it_key.data(), key.data(), 60)) {
        return {};
    }
    auto const value = it->value();
    MONAD_ASSERT(value.size() == 32);
    bytes32_t result;
    std::memcpy(result.bytes, value.data(), 32);
    return result;
}

void StateDb::write_accounts(Accounts const &accounts)
{
    (void)accounts;
}

void StateDb::write_storage(Storage const &storage)
{
    byte_string_fixed<60> key;
    for (auto const &[address, incarnations] : storage) {
        std::memcpy(&key[0], address.bytes, 20);
        for (auto const &[incarnation, locations] : incarnations) {
            boost::endian::store_big_u64(&key[20], incarnation);
            for (auto const &[location, value] : locations) {
                std::memcpy(&key[28], location.bytes, 32);
                batch_->Put(cfs_[2], to_slice(key), to_slice(value));
            }
        }
    }
}

void StateDb::write_account_history(
    absl::btree_map<uint64_t, AccountChanges> const &history)
{
    // TODO sort the keys first
    byte_string_fixed<28> key;
    for (auto const &[block_number, account_changes] : history) {
        boost::endian::store_big_u64(&key[20], block_number);
        for (auto const &[address, account] : account_changes) {
            std::memcpy(&key[0], address.bytes, 20);
            batch_->Put(cfs_[5], to_slice(key), to_slice(account));
        }
    }
}

void StateDb::write_storage_history(
    absl::btree_map<uint64_t, StorageChanges> const &history)
{
    // TODO sort the keys first
    byte_string_fixed<68> key;
    for (auto const &[block_number, storage_changes] : history) {
        boost::endian::store_big_u64(&key[60], block_number);
        for (auto const &[address, incarnations] : storage_changes) {
            std::memcpy(&key[0], address.bytes, 20);
            for (auto const &[incarnation, storage] : incarnations) {
                boost::endian::store_big_u64(&key[20], incarnation);
                for (auto const &[location, value] : storage) {
                    std::memcpy(&key[28], location.bytes, 32);
                    batch_->Put(cfs_[6], to_slice(key), to_slice(value));
                }
            }
        }
    }
}

void StateDb::revert()
{
    batch_->Clear();
}

void StateDb::commit()
{
    rocksdb::WriteOptions options;
    options.disableWAL = true;
    db_->Write(options, batch_.get());
}

MONAD_NAMESPACE_END
