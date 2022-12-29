#pragma once

#include <variant>
#include <concepts>

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/hash.hpp>
#include <monad/mpt/path.hpp>
#include <monad/mpt/branches.hpp>
#include <monad/rlp/rlp.hpp>

#include <range/v3/view/drop.hpp>
#include <range/v3/range/conversion.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{

using reference_type = hash256;
using reference_view_type = reference_type::string_view_type;

class BaseNode
{
private:
    Path path_to_node_;
    reference_type reference_;

public:
    constexpr BaseNode(PathView path_to_node, rlp::Encoding&& node_encoding)
        : path_to_node_(path_to_node)
        , reference_(
                (node_encoding.bytes().size() >= reference_type::static_capacity)
                ? keccak256(node_encoding.bytes())
                : hash256(node_encoding.bytes()))
    {
    }

    constexpr PathView path_to_node_view() const
    {
        return path_to_node_;
    }

    constexpr reference_view_type reference_view() const
    {
        return reference_;
    }
};

class BranchNode : public BaseNode
{
public:
    using ChildReferences = std::vector<reference_type>;
private:
    Branches branches_;
    ChildReferences child_references_;

public:
    constexpr BranchNode(PathView path_to_node,
                         Branches branches,
                         ChildReferences&& child_references)
        : BaseNode(path_to_node, calculate_rlp_encoding(branches, child_references))
        , branches_(branches)
        , child_references_(std::move(child_references))
    {
    }
private:
    rlp::Encoding calculate_rlp_encoding(
            Branches, ChildReferences const&)
    {
        // TODO: fill out once rlp encoding library is in
        return {};
    }
};


class ExtensionNode : public BaseNode
{
private:
    Path partial_path_;
    reference_type child_reference_;

public:
    constexpr ExtensionNode(PathView path_to_node,
                            PathView partial_path,
                            reference_view_type child_reference)
        : BaseNode(path_to_node, rlp::encode(
                    partial_path.compact_encoding<EncodeExtension>(),
                    child_reference))
        , partial_path_(partial_path)
        , child_reference_(child_reference)
    {
        assert(!partial_path_.empty());
    }
};

class LeafNode : public BaseNode
{
private:
    Path partial_path_; 
    rlp::Encoding value_;

public:
    LeafNode(PathView path_to_node,
             PathView partial_path,
             rlp::Encoding&& value)
        : BaseNode(path_to_node, rlp::encode(
                    partial_path.compact_encoding<EncodeLeaf>(),
                    value))
        , partial_path_(partial_path)
        , value_(std::move(value))
    {
    };
};

using Node = std::variant<ExtensionNode, BranchNode, LeafNode>;

} // namespace mpt

MONAD_NAMESPACE_END
