
#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/likely.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/util.hpp>

MONAD_MPT_NAMESPACE_BEGIN

using TraverseCallback = std::function<void(NibblesView, byte_string_view)>;

class RangedGetMachine : public TraverseMachine
{
    Nibbles path_;
    Nibbles const min_;
    Nibbles const max_;
    TraverseCallback callback_;

private:
    // This function is a looser version checking if min <= path < max. But it
    // will also return true if we should continue traversing down. Suppose we
    // have the range [0x00, 0x10] and we are at node 0x0. In that case the
    // path's size is less than the min, check if it's as substring.
    bool does_key_intersect_with_range(NibblesView const path)
    {
        bool const min_check = [this, path] {
            if (path.nibble_size() < min_.nibble_size()) {
                return NibblesView{min_}.starts_with(path);
            }
            else {
                return (path >= min_);
            }
        }();
        return min_check && (path < NibblesView{max_});
    }

public:
    RangedGetMachine(
        NibblesView const min, NibblesView const max, TraverseCallback callback)
        : path_{}
        , min_{min}
        , max_{max}
        , callback_(std::move(callback))
    {
    }

    virtual bool down(unsigned char const branch, Node const &node) override
    {
        if (MONAD_UNLIKELY(branch == INVALID_BRANCH)) {
            return true;
        }

        auto next_path =
            concat(NibblesView{path_}, branch, node.path_nibble_view());
        if (!does_key_intersect_with_range(next_path)) {
            return false;
        }

        path_ = std::move(next_path);
        if (node.has_value() && path_.nibble_size() >= min_.nibble_size()) {
            callback_(path_, node.value());
        }

        return true;
    }

    void up(unsigned char const branch, Node const &node) override
    {
        auto const path_view = NibblesView{path_};
        unsigned const rem_size = [&] {
            if (branch == INVALID_BRANCH) {
                return 0u;
            }
            constexpr unsigned BRANCH_SIZE = 1;
            return path_view.nibble_size() - BRANCH_SIZE -
                   node.path_nibble_view().nibble_size();
        }();
        path_ = path_view.substr(0, rem_size);
    }

    bool should_visit(Node const &, unsigned char const branch) override
    {
        auto const child = concat(NibblesView{path_}, branch);
        return does_key_intersect_with_range(child);
    }

    std::unique_ptr<TraverseMachine> clone() const override
    {
        return std::make_unique<RangedGetMachine>(*this);
    }
};

MONAD_MPT_NAMESPACE_END
