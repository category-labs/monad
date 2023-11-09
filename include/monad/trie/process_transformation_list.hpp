#pragma once

#include <monad/trie/config.hpp>
#include <monad/trie/node.hpp>
#include <monad/trie/transform.hpp>

#include <list>

MONAD_TRIE_NAMESPACE_BEGIN

template <typename TFunc>
[[nodiscard]] bytes32_t process_transformation_list_dead_simple(
    std::list<Node> &&list, TFunc finalize_and_emit)
{
    if (list.empty()) {
        return NULL_ROOT;
    }

    while (list.size() > 1) {
        for (auto it = list.begin(); it != list.end();) {
            if (std::next(it) == list.end()) {
                break;
            }

            auto &second = *it;
            auto &third = *std::next(it);

            auto const action = transform(
                it == list.begin()
                    ? tl::nullopt
                    : tl::make_optional<Nibbles const &>(
                          std::visit(&BaseNode::path_to_node, *std::prev(it))),
                std::visit(&BaseNode::path_to_node, second),
                std::visit(&BaseNode::path_to_node, third),
                std::next(it, 2) == list.end()
                    ? tl::nullopt
                    : tl::make_optional<Nibbles const &>(std::visit(
                          &BaseNode::path_to_node, *std::next(it, 2))));

            if (action == TransformAction::NONE) {
                std::advance(it, 1);
            }
            else if (action == TransformAction::CONCATENATE_TO_BRANCH) {
                MONAD_ASSERT(std::holds_alternative<Branch>(second));

                auto &branch = *std::get_if<Branch>(&second);

                std::visit(
                    [&](auto &child) {
                        // TODO: do not recalculate reference is parent doesnt
                        // change
                        finalize_and_emit(
                            child, branch.path_to_node.size() + 1);
                        branch.add_child(std::move(child));
                    },
                    third);

                auto const next = std::next(it, 2);
                list.erase(std::next(it));
                it = next;
            }
            else if (action == TransformAction::NEW_BRANCH) {
                std::visit(
                    [&](auto &left, auto &right) {
                        auto const parent_path =
                            left.path_to_node.prefix(longest_common_prefix_size(
                                left.path_to_node, right.path_to_node));

                        finalize_and_emit(left, parent_path.size() + 1);
                        finalize_and_emit(right, parent_path.size() + 1);

                        second = Branch(
                            parent_path, std::move(left), std::move(right));
                    },
                    second,
                    third);
                auto const next = std::next(it, 2);
                list.erase(std::next(it));
                it = next;
            }
        }
    }

    assert(list.size() == 1);
    return std::visit(
        [&finalize_and_emit](auto &node) {
            finalize_and_emit(node, 0);
            return get_root_hash(node);
        },
        list.front());
}

MONAD_TRIE_NAMESPACE_END
