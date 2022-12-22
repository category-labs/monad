#pragma once

#include <variant>
#include <concepts>
#include <bitset>
#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/mpt/path.hpp>
#include <monad/mpt/branches.hpp>
#include <monad/rlp/rlp.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{

class BaseNode
{
private:
    Path const path_to_node_;
    byte_string const reference_;

public:
    constexpr BaseNode(PathView path_to_node, byte_string_view reference)
        : path_to_node_(path_to_node)
        , reference_(reference)
    {
    }

    constexpr PathView path_to_node_view() const
    {
        return path_to_node_;
    }

    constexpr byte_string_view reference_view() const
    {
        return {};
    }
};

class ExtensionNode : public BaseNode
{
private:
    Path const partial_path_;
    byte_string const child_reference_;

public:
    constexpr ExtensionNode(PathView path_to_node, PathView path_to_child, byte_string_view child_reference)
        : BaseNode(path_to_node, calculate_reference())
        , partial_path_(partial_path_from_child(path_to_child))
        , child_reference_(child_reference)
    {
    }

private:
    PathView partial_path_from_child(PathView path_to_child) const
    {
        // TODO;
        return path_to_child;
    }
};

class BranchNode : public BaseNode
{
public:
    using ChildReferences = std::vector<byte_string>;
private:
    Branches const branches_;
    ChildReferences const child_references_;

    // TODO: populate this
    byte_string const reference_;
    
public:
    constexpr BranchNode(PathView path_to_node,
                         Branches branches,
                         ChildReferences&& child_references)
        : BaseNode(path_to_node)
        , branches_(branches)
        , child_references_(std::move(child_references))
    {
    }
};

class LeafNode : public BaseNode
{
private:
    Path const partial_path_; 
    rlp::Encoding const value_;

public:
    LeafNode(PathView path_to_node,
             PathView partial_path,
             rlp::Encoding&& value)
        : BaseNode(path_to_node)
        , partial_path_(partial_path)
        , value_(std::move(value))
    {
    };
private:
    byte_string calculate_reference(PathView) const
    {
    }
};

using Node = std::variant<ExtensionNode, BranchNode, LeafNode>;

} // namespace mpt

MONAD_NAMESPACE_END
