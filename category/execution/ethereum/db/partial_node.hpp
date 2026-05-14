// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <ankerl/unordered_dense.h>

#include <array>
#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

MONAD_NAMESPACE_BEGIN

/// An unresolved subtree whose contents are absent from the witness.
struct HashStub
{
    bytes32_t hash;
};

using NodeIndex = ankerl::unordered_dense::map<bytes32_t, byte_string>;

template <typename T>
concept LeafValue =
    requires(byte_string_view &enc, NodeIndex const &nodes, T const &v) {
        { T::decode(enc, nodes) } -> std::same_as<Result<T>>;
        { T::encode(v) } -> std::same_as<byte_string>;
    };

template <LeafValue V>
struct PartialNode;

/// Owning pointer to a child node. A null pointer represents an empty branch
/// slot (analogous to an absent nibble in a standard Ethereum branch node).
template <LeafValue V>
using ChildRef = std::unique_ptr<PartialNode<V>>;

template <LeafValue V>
struct BranchData
{
    std::array<ChildRef<V>, 16> children;
    std::optional<V> value;
};

template <LeafValue V>
struct ExtensionData
{
    mpt::Nibbles path;
    ChildRef<V> child;
};

template <LeafValue V>
struct LeafData
{
    mpt::Nibbles path;
    V value;
};

/// Four-way variant: branch, extension, leaf, or opaque hash stub.
template <LeafValue V>
struct PartialNode
{
    using Variant =
        std::variant<BranchData<V>, ExtensionData<V>, LeafData<V>, HashStub>;

    Variant v;

    PartialNode() = default;

    template <class T>
        requires std::constructible_from<Variant, T>
    explicit PartialNode(T &&x)
        : v(std::forward<T>(x))
    {
    }
};

MONAD_NAMESPACE_END
