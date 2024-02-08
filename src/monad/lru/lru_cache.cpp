#include <monad/lru/lru_cache.hpp>

#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

MONAD_NAMESPACE_BEGIN

LruCache::LruCache(Db& db)
: db_(db)
, accounts_(
      [this](Address addr){
          return db_.read_account(addr);
      },
      kAccountsCacheSize)
, storage_(
      [this](AddressKeyPair pair) {
          return db_.read_storage(pair.first, pair.second);
      },
      kStorageCacheSize)
{}

std::optional<Account>
LruCache::read_account(const Address& addr)
{
  return accounts_[addr].value();
}

bytes32_t
LruCache::read_storage(Address const &addr, bytes32_t const &key)
{
  return storage_[AddressKeyPair{addr, key}].value();
}

void
LruCache::commit(StateDeltas const & state)
{
    for (auto const &[addr, delta] : state) {
        auto const &acc = delta.account.second;
        if (acc.has_value()) {
            for (auto const &[key, delta] : delta.storage) {
	        auto handle = storage_[AddressKeyPair{addr, key}];
		handle.value() = delta.second;
            }
        }
	{
            auto handle = accounts_[addr];
            if (delta.account.first != delta.account.second) {
                handle.value() = delta.account.second;
                if (delta.account.second.has_value()) {
                    handle.value().value().incarnation = 0;
                }
            }
        }
    }
}

MONAD_NAMESPACE_END
