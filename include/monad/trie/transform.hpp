#pragma once

#include <monad/trie/config.hpp>
#include <monad/trie/nibbles.hpp>

#include <tl/optional.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

enum class TransformAction
{
    NONE,
    CONCATENATE_TO_BRANCH,
    NEW_BRANCH
};

[[nodiscard]] constexpr TransformAction transform(
    tl::optional<Nibbles const &> s_1, Nibbles const &s_2, Nibbles const &s_3,
    tl::optional<Nibbles const &> s_4)
{
    auto const len = longest_common_prefix_size(s_2, s_3);
    if ((!s_1 || len > longest_common_prefix_size(*s_1, s_2)) &&
        (!s_4 || len >= longest_common_prefix_size(s_3, *s_4))) {
        if (s_2.size() == len) {
            return TransformAction::CONCATENATE_TO_BRANCH;
        }
        return TransformAction::NEW_BRANCH;
    }

    return TransformAction::NONE;
}

MONAD_TRIE_NAMESPACE_END
