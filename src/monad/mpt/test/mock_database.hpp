#pragma once

#include "monad/rlp/rlp.hpp"

#include <concepts>

#include <exception>
#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/mpt/tree_store_interface.hpp>

#include <tl/expected.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
class MockDatabaseKey;

template <>
struct TreeStoreInterfaceTraits<MockDatabaseKey>
{
    using rep = std::vector<byte_string>;
    using iterator = rep::iterator;
};

// Used for testing the structure of the MPT. Ignores the value
class MockDatabaseKey : public TreeStoreInterface<MockDatabaseKey>
{
public:
    using traits = TreeStoreInterfaceTraits<MockDatabaseKey>;
    using rep = typename traits::rep;
    
private:
    rep storage_;

public:
    constexpr auto begin()
    {
        return storage_.begin();
    }

    constexpr auto end()
    {
        return storage_.end();
    }

    constexpr auto begin() const
    {
        return storage_.begin();
    }

    constexpr auto end() const
    {
        return storage_.end();
    }

    using TreeStoreInterface::insert;

    tl::expected<void, ErrorCode> insert(
            byte_string_view key, byte_string_view /*value*/)
    {
        storage_.push_back(byte_string{key});

        return {};
    }
};

} // namespace mpt

MONAD_NAMESPACE_END
