#pragma once

#include <absl/container/flat_hash_map.h>
#include <iterator>
#include <monad/core/bytes.hpp>
#include <monad/mpt/tree_store_interface.hpp>
#include <monad/config.hpp>
#include <monad/mpt/prefix_groups.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{

using KeyVal = std::pair<Path, byte_string_view>;

template <typename T>
concept EmitsKeyVal = requires (T object)
{
    {object()} -> std::same_as<KeyVal>;
};

template <typename T>
concept EmitsLatestBlock = requires (T object)
{
    {object.block_number()} -> std::same_as<uint64_t>;
};

template <typename T>
concept TreeInitializer = EmitsKeyVal<T> and EmitsLatestBlock<T>;

template <typename T>
concept TreeStore = std::derived_from<T, TreeStoreInterface>;

struct BuildLeafAndOrBranch {};
struct BuildExtensionAndOrBranch {};

template <typename T>
concept InitMode = std::same_as<T, BuildLeafAndOrBranch> or std::same_as<T, BuildExtensionAndOrBranch>;

template <TreeStore Storage>
class MerklePatriciaTree
{
private:
    Storage storage_;

public:
    // High level algorithm for initializing the MerklePatriciaTree is
    // as follows:
    // 1) Compute common prefixes between (prev, current, next)
    //                                       |_____| |______|
    //                                          |        |
    //                                          A        B
    // 2) if B.size() > A.size(), a new prefix group is starting
    // 3) (optional) add the extra digit (aka branch) to the current
    //    prefix group
    // 4) If Mode is currently BuildLeafAndOrBranch, emit a LEAF.
    //    If mode is BuildExtensionAndOrBranch, and the remainder (aka
    //    current with the max common prefix + branch chopped) is not
    //    empty, then emit an EXTENSION.
    // 5) if A.size() > B.size(), then at least one prefix group is
    //    being closed.
    //      1) Emit a BRANCH node, whose branches are taken from the
    //         current prefix group.
    //      2) Pop off the used prefix group
    //      3) If group closed was not the empty prefix (all keys),
    //         recurse back to the very beginning, with current = closed
    //         group, next = next (passed on), and Mode =
    //         BuildExtensionAndOrBranch. Recall, that the length of the
    //         previous max common prefix is being kept track by
    //         PrefixGroups
    MerklePatriciaTree(TreeInitializer auto initializer)
    {
        PrefixGroups groups;
    }

private:
    struct CommonPrefixSizes
    {
        size_t const prev;
        size_t const next;
        size_t const max;
    };

    struct WorkingPathViews
    {
        PathView current;
        PathView next;
    };

    struct InitState
    {
        PrefixGroups groups;

        // Each element is a node reference
        std::vector<Node> nodes;
    };

    CommonPrefixSizes get_common_prefix_sizes(
            WorkingPathViews const& paths, InitState& state)
    {
        auto const& [current, next] = paths;

        // Get the prefix lengths
        auto const [prev_prefix_size, _] = state.groups.get_current_group();
        auto const next_prefix_size = current.common_prefix_size(next); 
        auto const max_prefix_size = std::max(prev_prefix_size, next_prefix_size);

        // There is a bug in this code if this is not true
        assert(current.size() > max_prefix_size);

        return CommonPrefixSizes {
            .prev = prev_prefix_size,
            .next = next_prefix_size,
            .max = max_prefix_size
        };
    }

    void process_leaf(WorkingPathViews const& paths,
                      rlp::Encoding&& leaf_value,
                      InitState& state)
    {
        auto const& current = paths.current;

        auto const [common_prefix_sizes, size_of_path_to_node] = 
            optionally_add_branch_to_group(paths, state);

        auto const remainder = current.suffix(
                current.size() - size_of_path_to_node); 

        // Emit a leaf node
        //
        // Leaves should have a remainder, which in this case, is
        // also the partial path
        assert(not remainder.empty());

        auto const leaf_node = LeafNode(
                current.prefix(size_of_path_to_node),
                remainder,
                std::move(leaf_value));

        storage_.insert(leaf_node);
        state.nodes.emplace_back(std::move(leaf_node));
        
        optionally_close_out_prefix_group(paths, common_prefix_sizes, state);
    }

    // Optionally add branch to a new or existing prefix group.
    //
    // Returns the common prefix sizes and the number of nibbles
    // accounted for by the prefix group and branch
    std::pair<CommonPrefixSizes, size_t> optionally_add_branch_to_group(
            WorkingPathViews const& paths, InitState& state)
    {
        auto const& [current, next] = paths;
        auto const is_finalizing = next.empty();

        auto& [groups, _] = state;

        auto const common_prefix_sizes =
            get_common_prefix_sizes(paths, groups);

        // Add the extra branch character only if not finalizing or if
        // there is a working prefix group
        auto const add_branch_to_new_or_existing_group =
            !is_finalizing || !groups.empty();
        if (add_branch_to_new_or_existing_group) {
            groups.add_branch(common_prefix_sizes.max,
                              current[common_prefix_sizes.max]);
        }

        // Return the number of nibbles accounted for by the prefix group
        // and branch
        return std::make_pair(common_prefix_sizes,
                common_prefix_sizes.max +
                add_branch_to_new_or_existing_group);
    }

    // Close out the prefix group if we need to, generating branch node
    void optionally_close_out_prefix_group(
            WorkingPathViews const& paths,
            CommonPrefixSizes const& common_prefix_sizes,
            InitState& state)
    {
        auto const [current, next] = paths;
        auto const is_finalizing = next.empty();

        auto& [groups, nodes] = state;

        // Check if we need to close out the prefix group
        auto const is_closing_out =
            common_prefix_sizes.prev > common_prefix_sizes.next ||
            (is_finalizing && !groups.empty());

        if (!is_closing_out) {
            return;
        }

        // Prefix group must exist
        assert(!groups.empty());

        auto const [group_length, branches] = groups.get_current_group();

        // assert length of node references and that we actually have
        // branches
        assert(nodes.size() >= branches.size());
        assert(!branches.empty());

        // Construct a branch node, moving children node references over 
        auto start = std::prev(nodes.end(), branches.size());

        // Get list of child references
        //
        // Note: copies the reference into child_references
        using namespace std::placeholders;
        BranchNode::ChildReferences child_references;
        std::ranges::transform(
                start, nodes.end(),
                std::back_inserter(child_references),
                [](auto const& node) {
                     return std::visit(&BaseNode::reference_view, node);
                });

        auto const path_to_child = start->path_to_node();
        assert(!path_to_child.empty());

        auto const branch_node = BranchNode(
                path_to_child.prefix(path_to_child.size() - 1),
                branches,
                std::move(child_references));

        storage_.insert(branch_node);

        // Hijack the first element for the branch node reference 
        *start = std::move(branch_node);

        // Clean up nodes 
        //
        // Note: standard defines that behavior is noop if first == last
        // (aka std::next(start_ref_it) == nodes.end())
        nodes.erase(std::next(start), nodes.end());

        groups.pop_current_group();

        // We just closed the empty prefix, no work left
        if (MONAD_UNLIKELY(group_length == 0)) {
            return;
        }

        add_extension_and_or_branch(
                WorkingPathViews{
                    .current=current.prefix(group_length)
                    .next=next
                },
                state);
    }

    void add_extension_and_or_branch(WorkingPathViews const& paths, InitState& state)
    {
        auto const& [current, next] = paths;

        auto const [common_prefix_sizes, size_of_path_to_node] =
            optionally_add_branch_to_group(paths, state);

        auto const remainder = current.suffix(
                current.size() - size_of_path_to_node); 

        // Size of remainder is 0, no extension or branch nodes needed 
        if (remainder.size() == 0) {
            return;
        }

        // Does not make sense to generate an extension node if no nodes
        // currently
        assert(!state.nodes.empty());

        auto& child = state.nodes.back();
        auto const path_to_node = current.prefix(size_of_path_to_node);
        auto const extension_node = ExtensionNode(
            path_to_node,
            std::visit(&BaseNode::path_to_node_view, child),
            std::visit(&BaseNode::reference_view, child)
        );

        storage_.insert(extension_node);

        // hijack the child node and replace with extension node
        child = std::move(extension_node);

        optionally_close_out_prefix_group(
                paths, path_to_node, common_prefix_sizes, state);
    }
};
} // namespace mpt

MONAD_NAMESPACE_END
