
#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/mpt/config.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/util.hpp>

MONAD_MPT_NAMESPACE_BEGIN

using TraverseCallback = std::function<void(NibblesView, byte_string_view)>;

class RangedGetMachine : public TraverseMachine
{
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
        : min_{min}
        , max_{max}
        , callback_(std::move(callback))
    {
    }

    RangedGetMachine(RangedGetMachine const &parent, unsigned char branch)
        : TraverseMachine(parent, branch)
        , min_(parent.min_)
        , max_(parent.max_)
        , callback_(parent.callback_)
    {
    }

    RangedGetMachine(RangedGetMachine &&) = default;

    virtual void visit(unsigned char const, Node const &node) override
    {
        if (node.has_value() && path().nibble_size() >= min_.nibble_size()) {
            callback_(path(), node.value());
        }
    }

    bool should_visit_node(Node const &, unsigned char const) override
    {
        return does_key_intersect_with_range(path());
    }

    bool should_visit_child(Node const &, unsigned char const branch) override
    {
        auto const child = concat(path(), branch);
        return does_key_intersect_with_range(child);
    }

    std::unique_ptr<TraverseMachine> clone(unsigned char branch) const override
    {
        return std::make_unique<RangedGetMachine>(*this, branch);
    }
};

MONAD_MPT_NAMESPACE_END
