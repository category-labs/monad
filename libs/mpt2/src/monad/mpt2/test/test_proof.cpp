#include <monad/core/bytes.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt2/proof.hpp>
#include <monad/mpt2/rlp/item.hpp>
#include <monad/rlp/encode2.hpp>

#include <gtest/gtest.h>

#include <utility>

using namespace monad;
using namespace monad::literals;
using namespace monad::mpt;
using namespace monad::mpt2;

namespace
{
    // Trie has leaves
    //   0xAAAA
    //   0xAACA
    //   0xAACB

    // Simple Trie Structure Example:
    // ├── Ext[AA]
    // │      ├── Branch[A] -> Leaf[A]
    // │      └── Branch[C]
    // │           └── Branch[A] -> Leaf[]
    // │           └── Branch[B] -> Leaf[]
    //
    // Returns the proof for AACA
    // Generated using py-trie

    Nibbles const prefix{0xAACA_hex};
    auto const merkle_root = monad::to_bytes(
        0x14f1cab0a0c096296936c8f3225cea8a385eb15acbafb35a0b8a4a7764a8bf42_hex);
    std::array<byte_string, 4> const proof{
        0xe48200aaa054e8813349b140266b872f5ba88b7d957f9204d90a63270266fa79144dd90ce4_hex,
        0xf480808080808080808080c63a84deadbeef80dd80808080808080808080c62084deadbeefc62084deadbeef808080808080808080_hex,
        0xdd80808080808080808080c62084deadbeefc62084deadbeef8080808080_hex,
        0xc62084deadbeef_hex,
    };
}

TEST(Proof, Success)
{
    monad::byte_string encoded_proof;
    for (auto const &node : proof) {
        encoded_proof += node;
    }
    encoded_proof = rlp::encode_list2(encoded_proof);
    auto const res = verify_proof(prefix, merkle_root, encoded_proof);
    EXPECT_FALSE(res.has_error());
}

TEST(Proof, CorrectProofBadKey)
{
    monad::byte_string encoded_proof;
    for (auto const &node : proof) {
        encoded_proof += node;
    }
    encoded_proof = rlp::encode_list2(encoded_proof);
    Nibbles const bad_key{0xAABA_hex};
    auto const res = verify_proof(bad_key, merkle_root, encoded_proof);
    ASSERT_TRUE(res.has_error());
    EXPECT_EQ(res.assume_error(), ProofError::InvalidKey);
}

TEST(Proof, BadLeaf)
{
    monad::byte_string encoded_proof;
    auto bad_proof = proof;
    bad_proof[3][3] = ~bad_proof[3][3];
    for (auto const &node : bad_proof) {
        encoded_proof += node;
    }
    encoded_proof = rlp::encode_list2(encoded_proof);
    auto const res = verify_proof(prefix, merkle_root, encoded_proof);
    ASSERT_TRUE(res.has_error());
    EXPECT_EQ(res.assume_error(), ProofError::WrongMerkleProof);
}

TEST(Proof, BadExtension)
{
    monad::byte_string encoded_proof;
    auto bad_proof = proof;
    bad_proof[1][14] = ~bad_proof[1][14];
    for (auto const &node : bad_proof) {
        encoded_proof += node;
    }
    encoded_proof = rlp::encode_list2(encoded_proof);
    auto const res = verify_proof(prefix, merkle_root, encoded_proof);
    ASSERT_TRUE(res.has_error());
    EXPECT_EQ(res.assume_error(), ProofError::WrongMerkleProof);
}
