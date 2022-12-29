#pragma once

#include "monad/rlp/rlp.hpp"
#include <absl/container/btree_map.h>
#include <concepts>
#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/mpt/tree_store_interface.hpp>
#include <tl/expected.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
class MockDatabase;

template <>
struct TreeStoreInterfaceTraits<MockDatabase>
{
    struct TreeCmp {
        using is_transparent = void;

        bool operator()(byte_string const& first, byte_string const& second) const
        {
            return first < second;
        }

        bool operator()(byte_string const& first, byte_string_view second) const
        {
            return first < second;
        }

        bool operator()(byte_string_view first, byte_string const& second) const
        {
            return first < second;
        }
    };

    using rep = absl::btree_map<byte_string, byte_string, TreeCmp>;
    using iterator = rep::iterator;
};

class MockDatabase : public TreeStoreInterface<MockDatabase>
{
private:
    using traits = TreeStoreInterfaceTraits<MockDatabase>;
    using rep = typename traits::rep;
    
    rep storage_;

public:
    iterator begin()
    {
        return storage_.begin();
    }

    iterator end()
    {
        return storage_.end();
    }

    using TreeStoreInterface::insert;

    tl::expected<void, ErrorCode> insert(byte_string_view key, byte_string_view value)
    {
        auto const [_, duplicate] = storage_.try_emplace(key, value);

        if (duplicate) {
            return tl::unexpected(ErrorCode::DUPLICATE);
        }

        return {};
    }
};

} // namespace mpt

MONAD_NAMESPACE_END
