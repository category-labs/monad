
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
    Nibbles path_;
    NibblesView const min_;
    NibblesView const max_;
    TraverseCallback callback_;

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
        path_ = concat(NibblesView{path_}, branch, node.path_nibble_view());

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

    bool should_visit(Node const &node, unsigned char const branch) override
    {
        auto const next_path =
            concat(NibblesView{path_}, branch, node.path_nibble_view());

        bool const min_check = [this, next_path = NibblesView{next_path}] {
            if (next_path.nibble_size() < min_.nibble_size()) {
                return min_.starts_with(next_path);
            }
            else {
                return (next_path >= min_);
            }
        }();

        return min_check && (next_path < max_);
    }

    std::unique_ptr<TraverseMachine> clone() const override
    {
        return std::make_unique<RangedGetMachine>(*this);
    }
};

MONAD_MPT_NAMESPACE_END
