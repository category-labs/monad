#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/mpt/compute.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

using namespace monad::mpt;
using namespace monad::literals;

struct DummyCompute final : Compute
{
    // hash length = 1
    virtual unsigned compute_len(
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

    virtual unsigned compute_branch(unsigned char *, Node *) override
    {
        return 0;
    }

    virtual unsigned compute(unsigned char *buffer, Node *) override
    {
        buffer[0] = 0xa;
        return 1;
    }
};

auto const value = 0x12345678_hex;
auto const path = 0xabcdabcdabcdabcd_hex;

TEST(NodeTest, leaf)
{
    NibblesView const path1{1, 10, path.data()};
    Node::UniquePtr node{make_node(0, {}, path1, value, {}, 0)};

    EXPECT_EQ(node->mask, 0);
    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path1);
    EXPECT_EQ(node->get_mem_size(), 25);
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
    Node::UniquePtr node{
        create_node_with_children(comp, mask, children, path2, value, 0)};

    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 1);
    EXPECT_EQ(node->get_mem_size(), 61);
    EXPECT_EQ(node->get_disk_size(), 57);
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
    Node::UniquePtr node{
        create_node_with_children(comp, mask, children, path2, value, 0)};

    EXPECT_EQ(node->value(), value);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 2);
    EXPECT_EQ(node->get_mem_size(), 97);
    EXPECT_EQ(node->get_disk_size(), 85);
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
    Node::UniquePtr node{create_node_with_children(
        comp, mask, children, path2, std::nullopt, 0)};

    EXPECT_EQ(node->value_len, 0);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->get_mem_size(), 86);
    EXPECT_EQ(node->get_disk_size(), 74);
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
    Node::UniquePtr node{create_node_with_children(
        comp, mask, children, path2, std::nullopt, 0)};

    EXPECT_EQ(node->value_len, 0);
    EXPECT_EQ(node->path_nibble_view(), path2);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->get_mem_size(), 91);
    EXPECT_EQ(node->get_disk_size(), 79);
}

TEST(NodeTest, super_large_node)
{
    DummyCompute const comp{};
    size_t const value_len = 255 * 1024 * 1024;
    monad::byte_string value(value_len, 0);
    Node::UniquePtr node{make_node(0, {}, {}, value, {}, 0)};
    EXPECT_EQ(node->value_len, value_len);
    EXPECT_EQ(node->bitpacked.data_len, 0);
    EXPECT_EQ(node->get_mem_size(), value_len + sizeof(Node));
    EXPECT_EQ(
        node->get_disk_size(),
        value_len + sizeof(Node) + Node::disk_size_bytes);
}

TEST(NodeTest, children_iterator)
{
    auto f = [](uint16_t mask) {
        std::vector<std::pair<uint8_t, unsigned char>> children,
            expected_children;
        for (auto i = 0, j = 0; i < 16; ++i) {
            if (mask & (1u << i)) {
                expected_children.emplace_back(j++, i);
            }
        }
        for (auto [branch, index] : NodeChildrenRange{mask}) {
            children.emplace_back(branch, index);
        }
        ASSERT_EQ(expected_children, children)
            << std::hex << "mask: " << mask << std::dec;
    };

    uint16_t masks[] = {
        0b0u, 0b1u, 0b11u, 0b10101u, 0b101010u, 0b1111111111111111u};
    for (auto mask : masks) {
        ASSERT_NO_FATAL_FAILURE(f(mask));
    }
}
