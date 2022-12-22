#pragma once

#include <stack>
#include <cstddef>
#include <cassert>
#include <monad/config.hpp>
#include <monad/mpt/branches.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{

// PrefixGroups keeps track of a list of prefix groups that are
// currently open. The current working prefix group is always at the
// top of the stack
class PrefixGroups
{
private:
    struct PrefixGroup
    {
        size_t length;
        Branches branches;
    };
    std::stack<PrefixGroup> groups_;

public:
    constexpr void add_branch(size_t length, Nibble branch)
    {
        // we should either be adding to the newest one or creating
        // a new group
        //
        // should not be updating an old one
        assert(groups_.empty() || length >= groups_.top().length);

        if (!groups_.empty() && length == groups_.top().length) {
            auto& branches = groups_.top().branches;

            // branch should not already exist
            assert(not branches.branch_exists(branch));

            // if we are adding to the latest prefix group
            branches.add_branch(branch);
        } else {
            // if we are adding a new prefix group
            groups_.push(PrefixGroup{length, Branches{branch}});
        }
    }

    constexpr bool empty() const
    {
        return groups_.empty();
    }

    constexpr PrefixGroup get_current_group() const
    {
        // Make sure that we have a valid prefix group
        assert(not groups_.empty());

        return groups_.top();
    }

    constexpr void pop_current_group()
    {
        // Make sure that we have a valid prefix group
        assert(not groups_.empty());

        groups_.pop();
    }
};
} // namespace mpt

MONAD_NAMESPACE_END
