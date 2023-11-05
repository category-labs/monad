#include <monad/core/byte_string.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/node.hpp>

#include <gtest/gtest.h>

#include <variant>

using namespace monad;
using namespace monad::trie;

TEST(Node, Serialization)
{
    Leaf leaf;
    leaf.path_to_node = Nibbles(byte_string({0x01, 0x02, 0x03, 0x04}));
    leaf.reference = {0x01, 0x12, 0x34, 0x56, 0x78, 0x90};
    leaf.value = {0xde, 0xad, 0xbe, 0xef};
    leaf.finalize(0);
    auto bytes = serialize_node(leaf);
    auto node = deserialize_node({}, bytes);
    EXPECT_TRUE(std::holds_alternative<Leaf>(node));
    EXPECT_EQ(*std::get_if<Leaf>(&node), leaf);

    Branch branch;
    branch.path_to_node = Nibbles(byte_string({0x01, 0x02, 0x03, 0x04}));
    branch.reference = {0x01, 0x12, 0x34, 0x56, 0x78, 0x90};
    branch.finalize(0);
    bytes = serialize_node(branch);
    node = deserialize_node({}, bytes);
    EXPECT_TRUE(std::holds_alternative<Branch>(node));
    EXPECT_EQ(*std::get_if<Branch>(&node), branch);
}
