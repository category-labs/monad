#include <monad/db/state_db.hpp>

#include <monad/core/byte_string.hpp>

#include <silkworm/common/assert.hpp>
#include <silkworm/common/log.hpp>
#include <silkworm/common/rlp_err.hpp>
#include <silkworm/common/util.hpp>

#include <rocksdb/db.h>
#include <rocksdb/iterator.h>
#include <rocksdb/options.h>
#include <rocksdb/slice.h>
#include <rocksdb/status.h>
#include <rocksdb/write_batch.h>

#include <boost/endian/conversion.hpp>

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

static inline rocksdb::Slice to_slice(std::basic_string_view<uint8_t> const &s)
{
    return rocksdb::Slice{reinterpret_cast<char const *>(s.data()), s.size()};
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
                silkworm::log::Error() << s.ToString();
            }
            SILKWORM_ASSERT(s.ok());
            SILKWORM_ASSERT(db);
        }
        else {
            options.create_if_missing = true;
            rocksdb::Status s = rocksdb::DB::Open(options, path_.string(), &db);
            if (!s.ok()) {
                silkworm::log::Error() << s.ToString();
            }
            SILKWORM_ASSERT(s.ok());
            SILKWORM_ASSERT(db);
            cfs_.emplace_back(db->DefaultColumnFamily());
            for (auto const &cfd : cfds) {
                if (cfd.name == rocksdb::kDefaultColumnFamilyName) {
                    continue;
                }
                rocksdb::ColumnFamilyHandle *cf = nullptr;
                s = db->CreateColumnFamily(cfd.options, cfd.name, &cf);
                if (!s.ok()) {
                    silkworm::log::Error() << s.ToString();
                }
                SILKWORM_ASSERT(s.ok());
                SILKWORM_ASSERT(cf);
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
    rocksdb::PinnableSlice value;
    auto const status =
        db_->Get(rocksdb::ReadOptions{}, cfs_[1], to_slice(address), &value);
    if (status.IsNotFound()) {
        return std::nullopt;
    }
    SILKWORM_ASSERT(status.ok());
    if (value.empty()) {
        return std::nullopt;
    }
    auto const [account, err] = Account::from_encoded_storage(to_view(value));
    silkworm::rlp::success_or_throw(err);
    return account;
}

std::optional<Account> StateDb::read_account_history(
    address_t const &address, uint64_t const block_number)
{
    byte_string_fixed<28> key;
    std::memcpy(&key[0], address.bytes, 20);
    boost::endian::store_big_u64(&key[20], block_number);
    std::unique_ptr<rocksdb::Iterator> const it{
        db_->NewIterator(rocksdb::ReadOptions{}, cfs_[5])};
    it->SeekForPrev(to_slice(key));
    if (!it->Valid()) {
        return std::nullopt;
    }
    auto const it_key = it->key();
    SILKWORM_ASSERT(it_key.size() == 28);
    if (std::memcmp(it_key.data(), address.bytes, 20)) {
        return std::nullopt;
    }
    auto const value = it->value();
    if (value.empty()) {
        return std::nullopt;
    }
    auto const [account, err] = Account::from_encoded_storage(to_view(value));
    silkworm::rlp::success_or_throw(err);
    return account;
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
    SILKWORM_ASSERT(status.ok());
    SILKWORM_ASSERT(value.size() <= 32);
    bytes32_t result;
    std::memcpy(result.bytes + 32 - value.size(), value.data(), value.size());
    return result;
}

std::optional<bytes32_t> StateDb::read_storage_history(
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
        return std::nullopt;
    }
    auto const it_key = it->key();
    SILKWORM_ASSERT(it_key.size() == 68);
    if (std::memcmp(it_key.data(), key.data(), 60)) {
        return std::nullopt;
    }
    auto const value = it->value();
    SILKWORM_ASSERT(value.size() <= 32);
    bytes32_t result;
    std::memcpy(result.bytes + 32 - value.size(), value.data(), value.size());
    return result;
}

void StateDb::write_accounts(Accounts const &accounts)
{
    for (auto const &[address, account] : accounts) {
        if (account.has_value()) {
            auto const encoded_account = account->encode_for_storage();
            batch_->Put(cfs_[1], to_slice(address), to_slice(encoded_account));
        }
        else {
            batch_->Delete(cfs_[1], to_slice(address));
        }
    }
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
                batch_->Put(cfs_[2], to_slice(key), to_slice(silkworm::zeroless_view(value)));
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
    auto status = db_->Write(options, batch_.get());
    SILKWORM_ASSERT(status.ok());
    batch_->Clear();
}

MONAD_NAMESPACE_END
