// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/compute.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/util.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <vector>

using namespace monad::mpt;
using namespace monad::literals;

struct DummyCompute final : Compute
{
    // hash length = 1
    virtual unsigned compute_node_data_len(
        std::span<ChildData> const children, uint16_t const, NibblesView const,
        std::optional<monad::byte_string_view> const value) override
    {
        if (!value.has_value()) {
            return 0;
        }
        unsigned len = 0;
        for (auto const &i : children) {
            len += i.len;
        }
        return len >= 32 ? 32 : len;
    }

    virtual unsigned set_node_data(unsigned char *, unsigned) override
    {
        return 0;
    }

    virtual unsigned compute(unsigned char *const buffer, Node const &) override
    {
        buffer[0] = 0xa;
        return 1;
    }
};

auto const value = 0x12345678_bytes;
auto const path = 0xabcdabcdabcdabcd_bytes;

TEST(NodeTest, leaf)
{
    NibblesView const path1{1, 10, path.data()};
    Node::SharedPtr const node{make_node(0, {}, path1, value, {}, 0)};

    EXPECT_EQ(node->mask, 0);
    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path1);
    EXPECT_EQ(node->get_mem_size(), 32);
    EXPECT_EQ(node->get_disk_size(), 29);
}

TEST(NodeTest, leaf_single_branch)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[1];
    children[0].len = 1;
    children[0].data[0] = 0xa;
    children[0].branch = 0xc;
    children[0].ptr = make_node(0, {}, path1, value, {}, 0);
    NibblesView const path2{1, 10, path.data()};
    uint16_t const mask = 1u << 0xc;
    Node::SharedPtr const node{
        create_node_with_children(comp, mask, children, path2, value, 0)};

    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 1);
    EXPECT_EQ(node->get_mem_size(), 80);
    EXPECT_EQ(node->get_disk_size(), 65);
}

TEST(NodeTest, leaf_multiple_branches)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[2] = {ChildData{.len = 1}, ChildData{.len = 1}};
    children[0].data[0] = 0xa;
    children[1].data[0] = 0xa;
    children[0].branch = 0xa;
    children[1].branch = 0xc;
    children[0].ptr = make_node(0, {}, path1, value, {}, 0);
    children[1].ptr = make_node(0, {}, path1, value, {}, 0);

    NibblesView const path2{1, 10, path.data()};
    uint16_t const mask = (1u << 0xa) | (1u << 0xc);
    Node::SharedPtr const node{
        create_node_with_children(comp, mask, children, path2, value, 0)};

    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 2);
    EXPECT_EQ(node->get_mem_size(), 136);
    EXPECT_EQ(node->get_disk_size(), 101);
}

TEST(NodeTest, branch_node)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[2] = {ChildData{.len = 1}, ChildData{.len = 1}};
    children[0].data[0] = 0xa;
    children[1].data[0] = 0xa;
    children[0].branch = 0xa;
    children[1].branch = 0xc;
    children[0].ptr = make_node(0, {}, path1, value, {}, 0);
    children[1].ptr = make_node(0, {}, path1, value, {}, 0);

    NibblesView const path2{1, 1, path.data()}; // path2 is empty
    uint16_t const mask = (1u << 0xa) | (1u << 0xc);
    Node::SharedPtr const node{create_node_with_children(
        comp, mask, children, path2, std::nullopt, 0)};

    EXPECT_EQ(node->value_len, 0);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->get_mem_size(), 120);
    EXPECT_EQ(node->get_disk_size(), 90);
}

TEST(NodeTest, extension_node)
{
    DummyCompute comp{};
    NibblesView const path1{12, 16, path.data()};

    ChildData children[2] = {ChildData{.len = 1}, ChildData{.len = 1}};
    children[0].data[0] = 0xa;
    children[1].data[0] = 0xa;
    children[0].branch = 0xa;
    children[1].branch = 0xc;
    children[0].ptr = make_node(0, {}, path1, value, {}, 0);
    children[1].ptr = make_node(0, {}, path1, value, {}, 0);

    NibblesView const path2{1, 10, path.data()};
    uint16_t const mask = (1u << 0xa) | (1u << 0xc);
    Node::SharedPtr const node{create_node_with_children(
        comp, mask, children, path2, std::nullopt, 0)};

    EXPECT_EQ(node->value_len, 0);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->get_mem_size(), 128);
    EXPECT_EQ(node->get_disk_size(), 95);
}

TEST(NodeTest, super_large_node)
{
    DummyCompute const comp{};
    size_t const value_len = 255 * 1024 * 1024;
    monad::byte_string value(value_len, 0);
    Node::SharedPtr const node{make_node(0, {}, {}, value, {}, 0)};
    EXPECT_EQ(node->value_len, value_len);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->get_mem_size(), value_len + sizeof(Node));
    EXPECT_EQ(
        node->get_disk_size(),
        value_len + sizeof(Node) + Node::disk_size_bytes);
}

namespace
{
    Node::SharedPtr make_three_child_branch(DummyCompute &comp)
    {
        NibblesView const child_path{12, 16, path.data()};
        ChildData children[3] = {
            ChildData{.len = 1}, ChildData{.len = 1}, ChildData{.len = 1}};
        uint8_t const branches[3] = {0x1, 0x5, 0xc};
        compact_offset_pair const mins[3] = {
            {compact_virtual_chunk_offset_t::from_legacy(7),
             INVALID_COMPACT_VIRTUAL_OFFSET},
            {INVALID_COMPACT_VIRTUAL_OFFSET,
             compact_virtual_chunk_offset_t::from_legacy(0x12345)},
            {compact_virtual_chunk_offset_t::from_legacy(0xfffff - 2),
             compact_virtual_chunk_offset_t::from_legacy(99)}};
        for (unsigned i = 0; i < 3; ++i) {
            children[i].data[0] = static_cast<unsigned char>(0xa + i);
            children[i].branch = branches[i];
            children[i].ptr = make_node(0, {}, child_path, value, {}, 0);
            children[i].offset = chunk_offset_t{100 + i, 4096 * (i + 1)};
            children[i].subtrie_min_version = 1000 + i;
            children[i].min_offsets = mins[i];
        }
        uint16_t const mask = (1u << 0x1) | (1u << 0x5) | (1u << 0xc);
        NibblesView const node_path{1, 10, path.data()};
        return create_node_with_children(
            comp, mask, children, node_path, value, 77);
    }

    void expect_same_node(Node const &a, Node const &b)
    {
        ASSERT_EQ(a.mask, b.mask);
        EXPECT_EQ(a.version, b.version);
        EXPECT_EQ(a.path_nibble_view(), b.path_nibble_view());
        EXPECT_EQ(a.value(), b.value());
        EXPECT_EQ(a.data(), b.data());
        ASSERT_EQ(a.number_of_children(), b.number_of_children());
        for (unsigned i = 0; i < a.number_of_children(); ++i) {
            EXPECT_EQ(a.child_data_view(i), b.child_data_view(i));
            EXPECT_EQ(a.fnext(i), b.fnext(i));
            EXPECT_EQ(a.subtrie_min_version(i), b.subtrie_min_version(i));
            EXPECT_EQ(a.min_offset_fast(i), b.min_offset_fast(i));
            EXPECT_EQ(a.min_offset_slow(i), b.min_offset_slow(i));
        }
        EXPECT_EQ(a.get_disk_size(), b.get_disk_size());
    }
}

TEST(NodeLayout, size_word_carries_the_layout_version)
{
    EXPECT_EQ(encode_node_size_word(100), 100u | (1u << 31));
    auto const cur =
        decode_node_size_word(encode_node_size_word(Node::max_disk_size));
    EXPECT_EQ(cur.disk_size, Node::max_disk_size);
    EXPECT_EQ(cur.layout_version, NODE_LAYOUT_CURRENT);
    auto const old = decode_node_size_word(1u << 28);
    EXPECT_EQ(old.disk_size, 1u << 28);
    EXPECT_EQ(old.layout_version, NODE_LAYOUT_LEGACY);
    auto const other = decode_node_size_word((5u << 29) | 100);
    EXPECT_EQ(other.disk_size, 100u);
    EXPECT_EQ(other.layout_version, 5u);
}

TEST(NodeLayout, an_unknown_layout_version_aborts)
{
    testing::FLAGS_gtest_death_test_style = "threadsafe";
    DummyCompute comp{};
    auto const node = make_three_child_branch(comp);
    uint32_t const size = node->get_disk_size();
    std::vector<unsigned char> buf(size);
    serialize_node_to_buffer(buf.data(), size, *node, size, 0);
    uint32_t const word = size | (5u << NODE_LAYOUT_VERSION_SHIFT);
    std::memcpy(buf.data(), &word, sizeof(word));
    EXPECT_DEATH(
        (void)deserialize_node_from_buffer(buf.data(), buf.size()),
        "node layout version 5 is not one this binary reads");
}

TEST(NodeLayout, legacy_layout_decodes_to_the_same_node)
{
    DummyCompute comp{};
    auto const node = make_three_child_branch(comp);
    ASSERT_TRUE(node->min_offset_slow(0) == INVALID_COMPACT_VIRTUAL_OFFSET);
    ASSERT_TRUE(node->min_offset_fast(1) == INVALID_COMPACT_VIRTUAL_OFFSET);

    uint32_t const legacy_size = legacy_layout_disk_size(*node);
    EXPECT_EQ(legacy_size, node->get_disk_size() - 8 * 3);
    std::vector<unsigned char> buf(legacy_size);
    serialize_legacy_layout_node_to_buffer(
        buf.data(), legacy_size, *node, legacy_size, 0);
    EXPECT_EQ(monad::unaligned_load<uint32_t>(buf.data()), legacy_size);

    auto const decoded = deserialize_node_from_buffer(buf.data(), buf.size());
    expect_same_node(*node, *decoded);
}

TEST(NodeLayout, legacy_layout_split_writes_match_a_single_write)
{
    DummyCompute comp{};
    auto const node = make_three_child_branch(comp);
    uint32_t const legacy_size = legacy_layout_disk_size(*node);
    std::vector<unsigned char> whole(legacy_size);
    serialize_legacy_layout_node_to_buffer(
        whole.data(), legacy_size, *node, legacy_size, 0);
    for (unsigned const step : {1u, 3u, 7u, 64u}) {
        std::vector<unsigned char> pieces(legacy_size);
        for (unsigned off = 0; off < legacy_size; off += step) {
            serialize_legacy_layout_node_to_buffer(
                pieces.data() + off,
                std::min(step, legacy_size - off),
                *node,
                legacy_size,
                off);
        }
        EXPECT_EQ(pieces, whole) << "step " << step;
    }
}

TEST(NodeLayout, current_layout_round_trips_with_its_version)
{
    DummyCompute comp{};
    auto const node = make_three_child_branch(comp);
    uint32_t const size = node->get_disk_size();
    std::vector<unsigned char> buf(size);
    serialize_node_to_buffer(buf.data(), size, *node, size, 0);
    auto const word =
        decode_node_size_word(monad::unaligned_load<uint32_t>(buf.data()));
    EXPECT_EQ(word.layout_version, NODE_LAYOUT_CURRENT);
    EXPECT_EQ(word.disk_size, size);

    auto const decoded = deserialize_node_from_buffer(buf.data(), buf.size());
    expect_same_node(*node, *decoded);
}

TEST(NodeLayout, legacy_leaf_decodes_to_the_same_node)
{
    NibblesView const leaf_path{1, 10, path.data()};
    Node::SharedPtr const node{make_node(0, {}, leaf_path, value, {}, 0)};
    uint32_t const legacy_size = legacy_layout_disk_size(*node);
    ASSERT_EQ(legacy_size, node->get_disk_size());
    std::vector<unsigned char> buf(legacy_size);
    serialize_legacy_layout_node_to_buffer(
        buf.data(), legacy_size, *node, legacy_size, 0);
    EXPECT_EQ(monad::unaligned_load<uint32_t>(buf.data()), legacy_size);

    auto const decoded = deserialize_node_from_buffer(buf.data(), buf.size());
    expect_same_node(*node, *decoded);
}

TEST(NodeLayout, legacy_all_ones_min_offsets_decode_to_invalid)
{
    DummyCompute comp{};
    auto const node = make_three_child_branch(comp);
    unsigned const n = node->number_of_children();
    uint32_t const legacy_size = legacy_layout_disk_size(*node);
    std::vector<unsigned char> buf(legacy_size);
    serialize_legacy_layout_node_to_buffer(
        buf.data(), legacy_size, *node, legacy_size, 0);
    // Child 2 carries valid offsets on both lists; overwrite them as a
    // MONAD008 writer stored INVALID.
    unsigned const child = 2;
    ASSERT_NE(node->min_offset_fast(child), INVALID_COMPACT_VIRTUAL_OFFSET);
    ASSERT_NE(node->min_offset_slow(child), INVALID_COMPACT_VIRTUAL_OFFSET);
    size_t const legacy_offsets =
        Node::disk_size_bytes + sizeof(Node) + n * sizeof(chunk_offset_t);
    uint32_t const all_ones = 0xFFFFFFFF;
    for (unsigned const slot : {child, n + child}) {
        std::memcpy(
            buf.data() + legacy_offsets + slot * sizeof(uint32_t),
            &all_ones,
            sizeof(all_ones));
    }

    auto const decoded = deserialize_node_from_buffer(buf.data(), buf.size());
    EXPECT_EQ(decoded->min_offset_fast(child), INVALID_COMPACT_VIRTUAL_OFFSET);
    EXPECT_EQ(decoded->min_offset_slow(child), INVALID_COMPACT_VIRTUAL_OFFSET);
    for (unsigned i = 0; i < child; ++i) {
        EXPECT_EQ(decoded->min_offset_fast(i), node->min_offset_fast(i));
        EXPECT_EQ(decoded->min_offset_slow(i), node->min_offset_slow(i));
    }
    EXPECT_EQ(decoded->fnext(child), node->fnext(child));
    EXPECT_EQ(
        decoded->subtrie_min_version(child), node->subtrie_min_version(child));
}

// Only a zero-child node can sit at max_disk_size in the legacy layout and
// still decode, since decoding widens each child's min offsets.
TEST(NodeLayout, nodes_at_max_disk_size_decode_in_both_layouts)
{
    Node::SharedPtr node;
    {
        monad::byte_string big(
            Node::max_disk_size - sizeof(Node) - Node::disk_size_bytes, 0);
        for (size_t i = 0; i < big.size(); ++i) {
            big[i] = static_cast<unsigned char>(i ^ (i >> 8));
        }
        node = make_node(0, {}, {}, big, {}, 0);
    }
    uint32_t const size = node->get_disk_size();
    ASSERT_EQ(size, Node::max_disk_size);
    ASSERT_EQ(legacy_layout_disk_size(*node), size);
    std::vector<unsigned char> buf(size);
    auto const expect_decodes = [&](uint32_t const layout_version) {
        EXPECT_EQ(
            decode_node_size_word(monad::unaligned_load<uint32_t>(buf.data()))
                .layout_version,
            layout_version);
        auto const decoded =
            deserialize_node_from_buffer(buf.data(), buf.size());
        EXPECT_EQ(decoded->mask, 0);
        EXPECT_EQ(decoded->get_disk_size(), Node::max_disk_size);
        EXPECT_EQ(decoded->value_len, node->value_len);
        EXPECT_TRUE(decoded->value() == node->value());
    };

    serialize_node_to_buffer(buf.data(), size, *node, size, 0);
    expect_decodes(NODE_LAYOUT_CURRENT);
    serialize_legacy_layout_node_to_buffer(buf.data(), size, *node, size, 0);
    expect_decodes(NODE_LAYOUT_LEGACY);
}
