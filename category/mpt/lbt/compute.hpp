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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <concepts>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>

MONAD_MPT_NAMESPACE_BEGIN

namespace lbt
{
    template <class T>
    concept value_hasher = requires(Node const &node) {
        { T::hash(node) } -> std::same_as<bytes32_t>;
    };

    Commitment commit_children(Node const &);
    Commitment commit_children(std::span<ChildData const>);

    // Joins `prefix`, the key from its start down to at least the leaf's
    // start, with the leaf's `path` into its full key. The result may view
    // `prefix`, `path` or `storage`.
    NibblesView
    full_leaf_key(NibblesView prefix, NibblesView path, Nibbles &storage);

    // `key_prefix` is the key from its start down to at least the node's
    // start.
    template <value_hasher V>
    Commitment commit_node(Node const &node, NibblesView const key_prefix)
    {
        auto const path = node.path_nibble_view();
        if (!node.has_value()) {
            return commit_path(path, commit_children(node));
        }
        Nibbles storage;
        return commit_leaf(
            full_leaf_key(key_prefix, path, storage), V::hash(node));
    }

    // Keeps a value-bearing branch's commitment over its children in the
    // branch's own data, and gives its parent no hash: for nodes whose
    // commitment is read from their data, such as a table root.
    struct LbtDataCompute : Compute
    {
        virtual unsigned compute_node_data_len(
            std::span<ChildData> const children, uint16_t, NibblesView,
            std::optional<byte_string_view> const value) override
        {
            if (!value.has_value()) {
                return 0;
            }
            pending_ = commit_children(children);
            return sizeof(bytes32_t);
        }

        virtual unsigned set_node_data(
            unsigned char *const buffer, unsigned const max_size) override
        {
            MONAD_ASSERT(pending_.has_value());
            MONAD_ASSERT(max_size >= sizeof(bytes32_t));
            std::memcpy(buffer, pending_->hash().bytes, sizeof(bytes32_t));
            pending_.reset();
            return sizeof(bytes32_t);
        }

        virtual unsigned compute(unsigned char *, Node const &) override
        {
            return 0;
        }

    private:
        std::optional<Commitment> pending_;
    };

    template <value_hasher V>
    struct LbtCompute final : LbtDataCompute
    {
        // `prefix` is the key from its start down to the machine's depth. It
        // points into the machine, so the machine binds it again on every
        // get_compute(), right before the engine hashes.
        void bind_key(NibblesView const prefix) noexcept
        {
            key_prefix_ = prefix;
        }

        virtual unsigned
        compute(unsigned char *const buffer, Node const &node) override
        {
            auto const c = commit_node<V>(node, key_prefix_);
            std::memcpy(buffer, c.hash().bytes, sizeof(bytes32_t));
            return sizeof(bytes32_t);
        }

    private:
        NibblesView key_prefix_{};
    };
}

MONAD_MPT_NAMESPACE_END
