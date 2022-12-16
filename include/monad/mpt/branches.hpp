#pragma once

#include <bitset>
#include <cstddef>
#include <cassert>
#include <monad/config.hpp>
#include <monad/mpt/nibble.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
class Branches
{
private:
    constexpr static auto NUMBER_OF_BRANCHES = 16;
    std::bitset<NUMBER_OF_BRANCHES> branches_;
public:
    constexpr explicit Branches(Nibble branch)
    {
        add_branch(branch);
    }

    constexpr auto add_branch(Nibble branch) -> void
    {
        branches_.set(branch);
    }

    constexpr auto branch_exists(Nibble branch) -> bool
    {
        return branches_.test(branch);
    }

    constexpr auto rep() const
    {
        return branches_.to_ulong();
    }

    constexpr static auto capacity()
    {
        return NUMBER_OF_BRANCHES;
    }

    // Can make this constexpr in C++23
    bool operator==(Branches const&) const = default;
};

} // namespace mpt

MONAD_NAMESPACE_END
