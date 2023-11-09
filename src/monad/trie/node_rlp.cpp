#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>
#include <monad/trie/compact_encode.hpp>
#include <monad/trie/node.hpp>
#include <monad/trie/node_rlp.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_leaf(trie::Leaf const &leaf)
{
    return encode_list(
        encode_string(trie::compact_encode(leaf.partial_path(), true)),
        encode_string(leaf.value));
}

byte_string encode_branch(trie::Branch const &branch)
{
    auto const branch_rlp = encode_list(
        branch.children[0],
        branch.children[1],
        branch.children[2],
        branch.children[3],
        branch.children[4],
        branch.children[5],
        branch.children[6],
        branch.children[7],
        branch.children[8],
        branch.children[9],
        branch.children[10],
        branch.children[11],
        branch.children[12],
        branch.children[13],
        branch.children[14],
        branch.children[15],
        encode_string(byte_string{}));

    auto const partial_path = branch.partial_path();
    if (partial_path.empty()) {
        return branch_rlp;
    }

    return encode_list(
        encode_string(trie::compact_encode(partial_path, false)),
        to_node_reference(branch_rlp));
}

byte_string to_node_reference(byte_string_view rlp)
{
    if (rlp.size() < 32) {
        return byte_string(rlp);
    }

    auto const hash = ethash::keccak256(rlp.data(), rlp.size());
    return encode_string(to_byte_string_view(hash.bytes));
}

MONAD_RLP_NAMESPACE_END
