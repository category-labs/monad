#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/rlp/config.hpp>
#include <monad/trie/config.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

struct Leaf;
struct Branch;

MONAD_TRIE_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_leaf(trie::Leaf const &);
byte_string encode_branch(trie::Branch const &);
byte_string to_node_reference(byte_string_view rlp);

MONAD_RLP_NAMESPACE_END
