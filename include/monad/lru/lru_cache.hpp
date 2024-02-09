#pragma once

#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state_deltas.hpp>

#define TBB_PREVIEW_CONCURRENT_LRU_CACHE 1
#include <oneapi/tbb/concurrent_lru_cache.h>

MONAD_NAMESPACE_BEGIN

class LruCache {
  template <class Key, class Value>
  using TbbLruCache = oneapi::tbb::concurrent_lru_cache<Key, Value, std::function<Value(Key)>>;
  using AccountLruCache = TbbLruCache<Address, std::optional<Account>>;
  using AddressKeyPair = std::pair<Address, bytes32_t>;
  using StorageLruCache = TbbLruCache<AddressKeyPair, bytes32_t>;

  static const size_t kAccountsCacheSize = 10'000'000;
  static const size_t kStorageCacheSize = 10'000'000;

  Db& db_;
  AccountLruCache accounts_;
  StorageLruCache storage_;

public:
  explicit LruCache(Db& db);
  std::optional<Account> read_account(Address const &);
  bytes32_t read_storage(Address const &, bytes32_t const &);
  void commit(StateDeltas const &);
};

MONAD_NAMESPACE_END
