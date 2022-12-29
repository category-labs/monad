#pragma once

#include <monad/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/boost.hpp>

#include <tl/expected.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
template <typename T>
struct TreeStoreInterfaceTraits;

template<typename TreeStore>
class TreeStoreInterface
{
public:
    using traits = TreeStoreInterfaceTraits<TreeStore>;
    using iterator = typename traits::iterator;

    // iterator must be a birdirectional iterator
    //
    // Note: random access not a guaranteed characteristic of the
    // tree store
    static_assert(std::bidirectional_iterator<iterator>);

    MONAD_DEFINE_NESTED_ENUM_CLASS(ErrorCode, DUPLICATE);

    constexpr TreeStore& derived()
    {
        return *static_cast<TreeStore*>(this);
    }

    constexpr iterator begin()
    {
        return derived().begin();
    }

    constexpr iterator end()
    {
        return derived().end();
    }

    tl::expected<void, ErrorCode> insert(Node const& node, uint64_t block_number)
    {
        // NB: this current only works because Path is an array of nibbles
        // rather than an array of bytes. Not using a compact encoding here
        // because the standard one defines it to be valid only for
        // extension and leaf nodes. If we ever change the underlying rep
        // to be byte compacted then we need to adjust this
        auto const path_to_node =
            std::visit(&BaseNode::path_to_node_view, node);

        auto const key = path_to_node.underlying_bytes() +
            to_big_endian_byte_string(block_number);

        return derived().insert(key, std::visit(&BaseNode::reference_view, node));
    }

    // Node lower_bound(byte_string_view key,
    //                  std::optional<iterator> start = std::nullopt)
    // {
    //     derived().lower_bound(key, start);
    // }
};
} // namespace mpt

MONAD_NAMESPACE_END
