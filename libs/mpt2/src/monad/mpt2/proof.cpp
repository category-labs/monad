#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/likely.h>
#include <monad/mpt/merkle/node_reference.hpp>
#include <monad/mpt2/node.hpp>
#include <monad/mpt2/proof.hpp>
#include <monad/mpt2/rlp/item.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <utility>

using BOOST_OUTCOME_V2_NAMESPACE::success;
using namespace monad::mpt;

MONAD_MPT2_NAMESPACE_BEGIN

namespace
{
    template <typename T>
    Result<T> UnwrapItemOrError(rlp::RawItem const &item)
    {
        if (MONAD_LIKELY(std::holds_alternative<T>(item.value))) {
            return std::get<T>(item.value);
        }
        return ProofError::UnexpectedType;
    }

    bytes32_t to_node_reference(rlp::RawItem node)
    {
        bytes32_t h{};
        auto const rlp = rlp::encode_item(node);
        mpt::to_node_reference(rlp, h.bytes);
        return h;
    }

    Result<bytes32_t> to_key(rlp::RawItem node)
    {
        if (auto const *data = std::get_if<RawString>(&node.value);
            data != nullptr) {
            byte_string_view const key = *data;
            if (MONAD_UNLIKELY(key.size() > KECCAK256_SIZE)) {
                return ProofError::UnexpectedType;
            }
            if (key.size() == KECCAK256_SIZE) {
                return to_bytes(key);
            }
        }
        return to_node_reference(node);
    }
}

using rlp::RawItem;
using rlp::RawList;
using rlp::RawString;

Result<void> verify_proof(
    NibblesView const key, NibblesView const prefix,
    bytes32_t const &merkle_root, byte_string_view encoded_proof)
{
    if (!key.starts_with(prefix)) {
        return ProofError::InvalidKey;
    }

    BOOST_OUTCOME_TRY(
        auto const decoded_proof, rlp::decode_item(encoded_proof));
    BOOST_OUTCOME_TRY(
        auto const proof, UnwrapItemOrError<RawList>(decoded_proof));

    std::vector<bytes32_t> hashes;
    hashes.reserve(proof.size());
    for (size_t i = 1; i < proof.size(); ++i) {
        hashes[i] = to_node_reference(proof[i]);
    }
    hashes[0] = std::bit_cast<bytes32_t>(keccak256(rlp::encode_item(proof[0])));

    bytes32_t expected_hash = merkle_root;
    Nibbles path;

    for (size_t i = 0; i < proof.size(); ++i) {
        if (MONAD_UNLIKELY(expected_hash != hashes[i])) {
            return ProofError::WrongMerkleProof;
        }

        BOOST_OUTCOME_TRY(
            auto const &node, UnwrapItemOrError<RawList>(proof[i]));
        if (is_branch_node(node)) {
            unsigned char const branch = key.get(path.nibble_size());
            BOOST_OUTCOME_TRY(expected_hash, to_key(node[branch]));
            path = concat(path, branch);
        }
        else if (is_extension_node(node)) {
            BOOST_OUTCOME_TRY(
                auto const relpath, UnwrapItemOrError<RawString>(node[0]));
            BOOST_OUTCOME_TRY(expected_hash, to_key(node[1]));
            path = concat(path, decode_path(relpath));
        }
        else if (is_leaf_node(node)) {
            BOOST_OUTCOME_TRY(
                auto const relpath, UnwrapItemOrError<RawString>(node[0]));
            path = concat(path, decode_path(relpath));
            break;
        }
        else {
            return ProofError::UnexpectedType;
        }
    }
    if (MONAD_UNLIKELY(path != key)) {
        return ProofError::InvalidKey;
    }
    return success();
}

MONAD_MPT2_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::mpt2::ProofError>::mapping> const &
quick_status_code_from_enum<monad::mpt2::ProofError>::value_mappings()
{
    using monad::mpt2::ProofError;

    static std::initializer_list<mapping> const v = {
        {ProofError::Success, "success", {errc::success}},
        {ProofError::InvalidKey, "provided key doesn't match proof", {}},
        {ProofError::WrongMerkleProof, "computing merkle proof failed", {}},
        {ProofError::UnexpectedType, "invalid node type", {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
