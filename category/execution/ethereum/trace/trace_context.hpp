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
#include <category/core/monad_exception.hpp>
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

#if defined(__has_cpp_attribute)
    #if __has_cpp_attribute(clang::lifetimebound)
        #define MONAD_LIFETIMEBOUND [[clang::lifetimebound]]
    #elif __has_cpp_attribute(gnu::lifetimebound)
        #define MONAD_LIFETIMEBOUND [[gnu::lifetimebound]]
    #else
        #define MONAD_LIFETIMEBOUND
    #endif
#else
    #define MONAD_LIFETIMEBOUND
#endif

MONAD_NAMESPACE_BEGIN

namespace trace
{
    // This is an implementation detail of the tracing framework. This structure
    // represents a tracer, whose type information has been erased, thus
    // allowing us to store heterogeneous tracers in the same container.
    struct TypeErasedTracer
    {
        using DispatchFn =
            std::function<bool(std::type_index const &, void const *, void *)>;

        template <typename R>
            requires(Tracer<R> && !std::is_const_v<std::remove_reference_t<R>>)
        static TypeErasedTracer erase(R &r MONAD_LIFETIMEBOUND)
        {
            using Signature =
                typename std::remove_cvref_t<decltype(r)>::Signature;
            TypeErasedTracer erased_tracer{};
            erased_tracer.dispatch_ = [tracer = std::addressof(r)](
                                          std::type_index const &op_type,
                                          void const *raw_op,
                                          void *result) mutable -> bool {
                constexpr size_t num_ops = std::tuple_size_v<Signature>;

                auto dispatch_case = [&]<size_t I>(auto &self) mutable -> bool {
                    if constexpr (I == num_ops) {
                        return false;
                    }
                    else {
                        using Op = std::tuple_element_t<I, Signature>;
                        if (op_type == std::type_index(typeid(Op))) {
                            // TODO(dhil): This assertion is redundant if this
                            // object was applied by the tracing context
                            // object. It would be good to make this
                            // abstraction tighter, so that we know invoking
                            // this case is always well-defined.
                            MONAD_ASSERT_THROW(
                                raw_op, "Raw operation pointer is null");
                            auto const &op = *static_cast<Op const *>(raw_op);

                            if constexpr (std::same_as<
                                              return_type_t<Op>,
                                              void>) {
                                std::invoke(*tracer, op);
                            }
                            else {
                                // TODO(dhil): Similarly, this assertion is
                                // redundant.
                                MONAD_ASSERT_THROW(
                                    result, "Result pointer is null");
                                auto &answer =
                                    *static_cast<answer_type_t<Op> *>(result);
                                answer.emplace(std::invoke(*tracer, op));
                            }
                            return true;
                        }

                        return self.template operator()<I + 1>(self);
                    }
                };

                return dispatch_case.template operator()<0>(dispatch_case);
            };
            return erased_tracer;
        }

        bool dispatch(
            std::type_index const &op_type, void const *op, void *result) const
        {
            MONAD_ASSERT(dispatch_);
            return dispatch_(op_type, op, result);
        }

    private:
        TypeErasedTracer() = default;

        DispatchFn dispatch_;
    };

    static_assert(sizeof(TypeErasedTracer) == 32);
}

// The tracing context for a single transaction. Its interface offers one
// parametrized method `run` for performing a trace operation, which is then
// dispatched to the first suitable tracer in this context, returning the answer
// if any.
class TxTraceContext
{
public:
    constexpr explicit TxTraceContext()
        : tracers_{}
    {
    }

    explicit TxTraceContext(
        std::span<monad::trace::TypeErasedTracer const> const tracers
            MONAD_LIFETIMEBOUND);

    TxTraceContext(TxTraceContext const &) = default;
    TxTraceContext(TxTraceContext &&) = default;

    TxTraceContext &operator=(TxTraceContext const &) = default;
    TxTraceContext &operator=(TxTraceContext &&) = default;

    // Performs a syntactic trace operation which is interpreted by the first
    // suitable tracer in this context, returning the answer if any.
    template <typename Op, typename... Args>
        requires(std::is_class_v<Op> && std::constructible_from<Op, Args...>)
    auto run(Args &&...args) const -> answer_type_t<Op>
    {
        // C++'s type system mandates we handle `void` separately.
        if constexpr (std::same_as<answer_type_t<Op>, void>) {
            // Void fast exit. In particular, we do not bother materializing the
            // trace operation object.
            if (tracers_.empty()) {
                return;
            }
            Op op(std::forward<Args>(args)...);
            dispatch(std::type_index(typeid(Op)), &op, nullptr);
            return;
        }
        else {
            // Typed fast exit, returning the empty optional.
            if (tracers_.empty()) {
                return std::nullopt;
            }

            Op op(std::forward<Args>(args)...);
            answer_type_t<Op> answer{};
            dispatch(std::type_index(typeid(Op)), &op, &answer);
            return answer;
        }
    }

    // Returns the number of tracers in this context.
    size_t size() const;

private:
    void dispatch(
        std::type_index const &op_type, void const *op, void *result) const;

    std::span<monad::trace::TypeErasedTracer const> tracers_;
};

static_assert(sizeof(TxTraceContext) == 16);

// The tracing context for a block. The method `slice` slices this context into
// transaction tracing subcontexts.
class BlockTraceContext
{
public:
    template <typename R>
        requires Tracer<R>
    BlockTraceContext(
        size_t num_txs, std::span<R> const tracers MONAD_LIFETIMEBOUND)
        : num_txs_(num_txs)
        , tracers_{nullptr}
    {
        with_tracers(tracers);
    }

    explicit BlockTraceContext(size_t num_txs);

    template <typename R>
        requires Tracer<R>
    BlockTraceContext &
    with_tracers(std::span<R> const tracers MONAD_LIFETIMEBOUND)
    {
        using namespace monad::trace;
        // TODO(dhil): This requirement is stricter than it need be, as we can
        // always materialize the empty trace context `tracers.size() < i <
        // num_txs`. Though, I do not think there is a legitimate use-case for
        // that.
        MONAD_ASSERT(tracers.size() == num_txs_);

        if (!tracers_) {
            tracers_ =
                std::make_unique<std::vector<TypeErasedTracer>[]>(num_txs_);
            constexpr size_t default_tracers_per_tx = 2;
            for (size_t i = 0; i < num_txs_; ++i) {
                tracers_[i].reserve(default_tracers_per_tx);
            }
        }

        for (size_t i = 0; i < num_txs_; ++i) {
            tracers_[i].emplace_back(TypeErasedTracer::erase(tracers[i]));
        }
        return *this;
    }

    // Returns a tracing context for the ith transaction.
    TxTraceContext slice(size_t i) const;

    // Tests whether the tracing context can be sliced n-ways.
    bool can_slice(size_t n) const;

    // Returns the number of tracers installed per transaction in this context.
    size_t tracers_per_tx() const;

private:
    size_t const num_txs_;
    std::unique_ptr<std::vector<monad::trace::TypeErasedTracer>[]> tracers_;
};

static_assert(sizeof(BlockTraceContext) == 16);

namespace trace
{
    template <typename Op, typename... Args>
        requires(std::is_class_v<Op> && std::constructible_from<Op, Args...>)
    inline auto emit(monad::TxTraceContext const &tr_ctx, Args &&...args)
        -> answer_type_t<Op>
    {
        return tr_ctx.template run<Op>(std::forward<Args>(args)...);
    }
}

MONAD_NAMESPACE_END

#undef MONAD_LIFETIMEBOUND
