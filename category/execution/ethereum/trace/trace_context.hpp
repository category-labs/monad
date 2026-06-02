// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>

#include <cstddef>
#include <functional>
#include <memory>
#include <optional>
#include <span>
#include <tuple>
#include <type_traits>
#include <typeindex>
#include <utility>
#include <vector>

namespace monad::trace
{
    // This is an implementation detail of the tracing framework. This structure
    // represents a runner, whose type information has been erased, thus
    // allowing us to store heterogeneous runners in the same container.
    struct TypeErasedRunner
    {
        struct VTableEntry
        {
            std::type_index tag{typeid(void)};
            std::function<void(void const *, void *)> fn{nullptr};
        };

        TypeErasedRunner() = delete;

        template <typename R>
            requires Runner<R>
        static TypeErasedRunner erase(R &r)
        {
            using Signature =
                typename std::remove_cvref_t<decltype(r)>::Signature;
            constexpr size_t num_ops = std::tuple_size_v<Signature>;

            TypeErasedRunner runner{num_ops};
            runner.for_each_op<Signature, 0, num_ops>(
                std::forward<decltype(r)>(r));
            return runner;
        }

    private:
        TypeErasedRunner(size_t vtable_size);

        template <typename Signature, size_t I, size_t N>
        void for_each_op(Runner auto &r)
        {
            if constexpr (I < N) {
                using Op = std::tuple_element_t<I, Signature>;

                // Install the operation case.
                vtable_[I] = VTableEntry{
                    std::type_index(typeid(Op)),
                    [runner = std::forward<decltype(r)>(r)](
                        void const *raw_op, void *result) mutable {
                        // TODO(dhil): This assertion is redundant if this
                        // object was applied by the tracing context object. It
                        // would be good to make this abstraction tighter, so
                        // that we know invoking this case is always
                        // well-defined.
                        MONAD_ASSERT(raw_op);
                        auto const &op = *static_cast<Op const *>(raw_op);

                        if constexpr (std::same_as<return_type_t<Op>, void>) {
                            std::invoke(runner, op);
                        }
                        else {
                            // TODO(dhil): Similarly, this assertion is
                            // redundant.
                            MONAD_ASSERT(result);
                            auto &answer =
                                *static_cast<answer_type_t<Op> *>(result);
                            answer.emplace(std::invoke(runner, op));
                        }
                    }};
                for_each_op<Signature, I + 1, N>(r);
            }
        }

    public:
        // NOTE(dhil): We expect `vtable_.size()` to be small (e.g. < 10), so we
        // use a dense representation and linear scan instead of a hash map.
        std::unique_ptr<VTableEntry[]> vtable_;
        size_t const vtable_size_;
    };

    static_assert(sizeof(TypeErasedRunner) == 16);
}

MONAD_NAMESPACE_BEGIN

// The tracing context for a single transaction. Its interface offers one
// parametrized method `perform` for performing a trace operation, which is then
// dispatched to the first suitable runner in this context, returning the answer
// if any.
class TxTraceContext
{
public:
    constexpr explicit TxTraceContext()
        : runners_{}
    {
    }

    explicit TxTraceContext(
        std::span<monad::trace::TypeErasedRunner const> const runners);

    // // Performs a syntactic trace operation which is interpreted by _all_
    // // suitable runners in this context.
    // template <typename Op, typename... Args>
    //     requires(std::is_class_v<Op> && std::constructible_from<Op, Args...>)
    // void emit(Args &&...args) const
    // {
    //     // Fast exit if there are no runners. In particular, we do not bother
    //     // materializing the trace operation object.
    //     if (runners_.empty()) {
    //         return;
    //     }

    //     Op op(std::forward<Args>(args)...);
    //     dispatch_all(std::type_index(typeid(Op)), &op);
    // }

    // Performs a syntactic trace operation which is interpreted by the first
    // suitable runner in this context, returning the answer if any.
    template <typename Op, typename... Args>
        requires(std::is_class_v<Op> && std::constructible_from<Op, Args...>)
    auto run(Args &&...args) const -> answer_type_t<Op>
    {
        // C++'s type system mandates we handle `void` separately.
        if constexpr (std::same_as<answer_type_t<Op>, void>) {
            // Void fast exit. In particular, we do not bother materializing the
            // trace operation object.
            if (runners_.empty()) {
                return;
            }
            Op op(std::forward<Args>(args)...);
            dispatch(std::type_index(typeid(Op)), &op, nullptr);
            return;
        }
        else {
            // Typed fast exit, returning the empty optional.
            if (runners_.empty()) {
                return std::nullopt;
            }

            Op op(std::forward<Args>(args)...);
            answer_type_t<Op> answer{};
            dispatch(std::type_index(typeid(Op)), &op, &answer);
            return answer;
        }
    }

    // Returns the number of runners in this context.
    size_t size() const;

private:
    void dispatch(
        std::type_index const &op_type, void const *op, void *result) const;

    std::span<monad::trace::TypeErasedRunner const> const runners_;
};

static_assert(sizeof(TxTraceContext) == 16);

// The tracing context for a block. The method `slice` slices this context into
// transaction tracing subcontexts.
class BlockTraceContext
{
public:
    template <typename R>
        requires Runner<R>
    BlockTraceContext(size_t num_txs, std::span<R> const runners)
        : num_txs_(num_txs)
        , runners_{nullptr}
    {
        with_runners(runners);
    }

    BlockTraceContext(size_t num_txs);

    template <typename R>
        requires Runner<R>
    BlockTraceContext &with_runners(std::span<R const> const runners)
    {
        using namespace monad::trace;
        // TODO(dhil): This requirement is stricter than it need be, as we can
        // always materialize the empty trace context `runners.size() < i <
        // num_txs`. Though, I do not think there is a legitimate use-case for
        // that.
        MONAD_ASSERT(runners.size() == num_txs_);

        if (!runners_) {
            runners_ =
                std::make_unique<std::vector<TypeErasedRunner>[]>(num_txs_);
            constexpr size_t default_runners_per_tx = 2;
            for (size_t i = 0; i < num_txs_; ++i) {
                runners_[i].reserve(default_runners_per_tx);
            }
        }

        for (size_t i = 0; i < num_txs_; ++i) {
            runners_[i].emplace_back(TypeErasedRunner::erase(runners[i]));
        }
        return *this;
    }

    // Returns a tracing context for the ith transaction.
    TxTraceContext slice(size_t i) const;

    // Tests whether the tracing context can be sliced n-ways.
    bool can_slice(size_t n) const;

    // Returns the number of runners installed per transaction in this context.
    size_t runners_per_tx() const;

private:
    size_t const num_txs_;
    std::unique_ptr<std::vector<monad::trace::TypeErasedRunner>[]> runners_;
};

static_assert(sizeof(BlockTraceContext) == 16);

MONAD_NAMESPACE_END
