#include <monad/state3/transient_storage.hpp>

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>

MONAD_NAMESPACE_BEGIN

bytes32_t
TransientStorage::get(Address const &address, bytes32_t const &key) const
{
    auto const addr_it = current_.find(address);
    if (addr_it == current_.end()) {
        return {};
    }

    auto const value_it = addr_it->second.find(key);
    if (value_it == addr_it->second.end()) {
        return {};
    }

    return value_it->second;
}

void TransientStorage::put(
    Address const &address, bytes32_t const &key, bytes32_t const &value)
{
    journal_.emplace_back(address, key, get(address, key));
    current_[address][key] = value;
}

void TransientStorage::commit()
{
    MONAD_ASSERT(!checkpoints_.empty());

    checkpoints_.pop_back();
}

void TransientStorage::checkpoint()
{
    checkpoints_.push_back(journal_.size());
}

void TransientStorage::revert()
{
    MONAD_ASSERT(!checkpoints_.empty());

    auto const last_checkpoint = checkpoints_.back();
    checkpoints_.pop_back();

    auto const n_since_last_checkpoint =
        static_cast<int64_t>(journal_.size() - last_checkpoint);

    auto const begin = journal_.rbegin();
    auto const end = journal_.rbegin() + n_since_last_checkpoint;

    for (auto it = begin; it != end; ++it) {
        auto const &[addr, key, value] = *it;
        current_[addr][key] = value;
    }

    journal_.erase(
        journal_.begin() + static_cast<int64_t>(last_checkpoint),
        journal_.end());
}

MONAD_NAMESPACE_END
