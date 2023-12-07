#pragma once

#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/rlp/encode2.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/node_rlp.hpp>

#include <ethash/keccak.hpp>

#include <bit>
#include <cassert>
#include <cstring>
#include <limits>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

MONAD_TRIE_NAMESPACE_BEGIN

struct BaseNode
{
    enum class Type : uint8_t
    {
        DELETED = 0,
        BRANCH = 1,
        LEAF = 2
    };

    // parent + branch
    std::optional<uint8_t> key_size;
    Nibbles path_to_node;
    byte_string reference;

    constexpr BaseNode() = default;

    [[nodiscard]] constexpr NibblesView partial_path() const
    {
        assert(key_size);
        return path_to_node.substr(*key_size);
    }

    [[nodiscard]] constexpr bool operator==(BaseNode const &) const = default;

protected:
    constexpr BaseNode(NibblesView const &path_to_node)
        : path_to_node(path_to_node)
    {
    }
};

struct Branch : public BaseNode
{
    std::array<byte_string, 16> children = {
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
        rlp::EMPTY_STRING,
    };

    constexpr Branch() = default;
    constexpr Branch(Branch &&) = default;
    constexpr Branch(Branch const &) = default;

    constexpr Branch(
        NibblesView path_to_node, BaseNode const &first, BaseNode &&second)
        : BaseNode(path_to_node)
    {
        auto const i = path_to_node.size();

        assert(i < first.path_to_node.size());
        assert(i < second.path_to_node.size());
        assert(first.path_to_node[i] != second.path_to_node[i]);
        assert(first.reference != rlp::EMPTY_STRING);
        assert(second.reference != rlp::EMPTY_STRING);

        children[first.path_to_node[i]] = std::move(first.reference);
        children[second.path_to_node[i]] = std::move(second.reference);
    }

    [[nodiscard]] constexpr Nibbles first_child() const
    {
        auto const it = std::ranges::find_if_not(
            children, [](auto const &ref) { return ref == rlp::EMPTY_STRING; });

        assert(it != children.end());

        auto ret = path_to_node;
        ret.push_back(static_cast<byte_string::value_type>(
            std::distance(children.begin(), it)));
        return ret;
    }

    [[nodiscard]] constexpr byte_string::value_type last_branch() const
    {
        auto const it = std::ranges::find_if_not(
            children.rbegin(), children.rend(), [](auto const &ref) {
                return ref == rlp::EMPTY_STRING;
            });
        assert(it != children.rend());

        return static_cast<byte_string::value_type>(
            std::distance(children.begin(), it.base()) - 1);
    }

    void finalize(uint8_t s)
    {
        key_size = s;
        reference = rlp::to_node_reference(rlp::encode_branch(*this));
    }

    constexpr void add_child(BaseNode &&child)
    {
        assert(child.path_to_node.size() > path_to_node.size());
        assert(child.reference != rlp::EMPTY_STRING);

        auto const branch = child.path_to_node[path_to_node.size()];

        assert(branch <= 0xF);

        children[branch] = std::move(child.reference);
    }

    [[nodiscard]] constexpr bool operator==(Branch const &) const = default;
    [[nodiscard]] constexpr Branch &operator=(Branch &&) = default;
};

struct Leaf : public BaseNode
{
    byte_string value;

    constexpr Leaf() = default;
    constexpr Leaf(Leaf &&) = default;
    constexpr Leaf(Leaf const &) = default;

    constexpr Leaf(NibblesView const &path_to_node, byte_string_view value)
        : BaseNode(path_to_node)
        , value(value)
    {
    }

    void finalize(uint8_t s)
    {
        key_size = s;
        reference = rlp::to_node_reference(rlp::encode_leaf(*this));
    }

    [[nodiscard]] constexpr bool operator==(Leaf const &) const = default;
    [[nodiscard]] constexpr Leaf &operator=(Leaf &&) = default;
};

using Node = std::variant<Leaf, Branch>;

template <typename T>
concept LeafOrBranch = std::same_as<T, Leaf> || std::same_as<T, Branch>;

template <LeafOrBranch T>
constexpr byte_string serialize_node(T const &node)
{
    byte_string buffer;

    if constexpr (std::same_as<T, Leaf>) {
        buffer.push_back(static_cast<uint8_t>(BaseNode::Type::LEAF));
    }
    else {
        buffer.push_back(static_cast<uint8_t>(BaseNode::Type::BRANCH));
    }

    serialize_nibbles(buffer, Nibbles{node.partial_path()});

    assert(node.reference.size() <= 33);
    buffer.push_back(
        static_cast<byte_string::value_type>(node.reference.size()));
    buffer += node.reference;

    if constexpr (std::same_as<T, Leaf>) {
        buffer += node.value;
    }
    else {
        for (auto const &child : node.children) {
            assert(child.size() >= 1 && child.size() <= 33);
            buffer += static_cast<byte_string::value_type>(child.size());
            buffer += child;
        }
    }

    return buffer;
}

namespace impl
{
    [[nodiscard]] constexpr size_t deserialize_base_node(
        BaseNode &node, monad::trie::Nibbles const &key,
        monad::byte_string_view bytes)
    {
        MONAD_ASSERT(!bytes.empty());

        node.key_size = key.size();

        auto const [partial_path, bytes_processed] =
            monad::trie::deserialize_nibbles(bytes);
        node.path_to_node = key + partial_path;

        using diff_t = decltype(bytes)::difference_type;
        assert(bytes_processed <= std::numeric_limits<diff_t>::max());

        auto it =
            std::next(bytes.begin(), static_cast<diff_t>(bytes_processed));
        MONAD_ASSERT(it != bytes.end());
        uint8_t const size = *it;

        std::advance(it, 1);
        MONAD_ASSERT(std::distance(it, bytes.end()) >= size);

        auto const end = std::next(it, size);
        node.reference = monad::byte_string_view(it, end);

        assert(bytes.begin() < end);

        return static_cast<size_t>(std::distance(bytes.begin(), end));
    }
}

[[nodiscard]] constexpr Node
deserialize_node(Nibbles const &key, byte_string_view value)
{

    MONAD_ASSERT(!value.empty());

    auto it = value.begin();

    if (static_cast<BaseNode::Type>(*it) == BaseNode::Type::BRANCH) {
        Branch branch;

        std::advance(it, 1);
        auto const bytes_processed = impl::deserialize_base_node(
            branch, key, byte_string_view(it, value.end()));
        std::advance(it, bytes_processed);

        for (size_t i = 0; i < branch.children.size(); ++i) {
            MONAD_ASSERT(it != value.end());

            uint8_t const size = *it;

            auto const start = std::next(it);
            MONAD_ASSERT(std::distance(start, value.end()) >= size);
            auto const end = std::next(start, size);
            branch.children[i] = byte_string_view(start, end);

            it = end;
        }

        MONAD_ASSERT(it == value.end());

        return branch;
    }

    MONAD_ASSERT(static_cast<BaseNode::Type>(*it) == BaseNode::Type::LEAF);

    Leaf leaf;
    std::advance(it, 1);
    auto const bytes_processed = impl::deserialize_base_node(
        leaf, key, byte_string_view(it, value.end()));
    std::advance(it, bytes_processed);

    leaf.value = byte_string_view(it, value.end());

    return leaf;
}

[[nodiscard]] constexpr bytes32_t get_root_hash(Node const &var)
{
    return std::visit(
        [&](auto const &node) {
            if (node.reference.size() == (1 + sizeof(bytes32_t))) {
                bytes32_t root_hash;
                std::memcpy(
                    root_hash.bytes, &node.reference[1], sizeof(bytes32_t));
                return root_hash;
            }

            return std::bit_cast<bytes32_t>(ethash::keccak256(
                node.reference.data(), node.reference.size()));
        },
        var);
}

MONAD_TRIE_NAMESPACE_END

template <>
struct fmt::formatter<monad::trie::Branch> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::trie::Branch const &branch, FormatContext &ctx) const
    {
        auto const format = [&](size_t i) {
            return fmt::format(
                "0x{:02x}",
                fmt::join(std::as_bytes(std::span(branch.children[i])), ""));
        };
        std::array const strings = {
            format(0),
            format(1),
            format(2),
            format(3),
            format(4),
            format(5),
            format(6),
            format(7),
            format(8),
            format(9),
            format(10),
            format(11),
            format(12),
            format(13),
            format(14),
            format(15),
        };
        static_assert(
            strings.size() == std::tuple_size<decltype(branch.children)>());

        fmt::format_to(
            ctx.out(),
            "Branch{{key_size={:d} path_to_node={} reference=0x{:02x} "
            "branches={::}}}",
            branch.key_size,
            branch.path_to_node,
            fmt::join(std::as_bytes(std::span(branch.reference)), ""),
            strings);

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::trie::Leaf> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::trie::Leaf const &leaf, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Leaf{{key_size={:d} path_to_node={} reference=0x{:02x} "
            "value=0x{:02x}}}",
            leaf.key_size,
            leaf.path_to_node,
            fmt::join(std::as_bytes(std::span(leaf.reference)), ""),
            fmt::join(std::as_bytes(std::span(leaf.value)), ""));
        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::trie::Node> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::trie::Node const &update, FormatContext &ctx) const
    {
        std::visit(
            [&ctx](auto const &u) { fmt::format_to(ctx.out(), "{}", u); },
            update);
        return ctx.out();
    }
};
