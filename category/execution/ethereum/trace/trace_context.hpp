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

#include <algorithm>
#include <array>
#include <cstddef>
#include <functional>
#include <memory>
#include <optional>
#include <span>
#include <string_view>
#include <tuple>
#include <type_traits>
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
    // NOTE(dhil): A previous compile-time mechanism for obtaining a unique
    // runtime identity for a trace command relied on RTTI, which is unavailable
    // on the zkVM). This approach uses the address of a statically allocated
    // descriptor to uniquely identify each operation type at runtime. The
    // descriptor includes a name too, but this is only to be used for
    // diagnostic purposes, because distinct types may share a spelling, e.g.
    // anonymous-namespace types in different translation units.
    struct OpInfo
    {
        // Null-terminated, so `name.data()` is also a valid C string.
        std::string_view name;
    };

    using OpId = OpInfo const *;

    namespace detail
    {
        template <typename Op>
        consteval std::string_view pretty_function()
        {
            return __extension__ __PRETTY_FUNCTION__;
        }

        // Extracts the spelling of `Op` from `pretty_function<Op>()` by
        // measuring the compiler-specific decoration around a known type.
        template <typename Op>
        consteval std::string_view type_name()
        {
            constexpr std::string_view probe = pretty_function<void>();
            constexpr size_t prefix = probe.find("void");
            constexpr size_t suffix = probe.size() - prefix - 4;
            constexpr std::string_view raw = pretty_function<Op>();
            return raw.substr(prefix, raw.size() - prefix - suffix);
        }

        // Copies the name out of the decorated function signature, so that
        // only the spelling of `Op` is retained in the binary.
        //
        // NOTE(dhil): This is a slight binary size optimization, as it avoids
        // storing the full decorated function signature in the binary. We can
        // consider removing this optimization if binary size is not a concern.
        // Alternatively, we can eliminate textual names entirely.
        template <typename Op>
        consteval auto make_op_name()
        {
            constexpr std::string_view name = type_name<Op>();
            std::array<char, name.size() + 1> storage{};
            std::ranges::copy(name, storage.begin());
            return storage;
        }

        template <typename Op>
        inline constexpr auto op_name = make_op_name<Op>();

        // NOTE(dhil): This is deliberately non-const! A writable object cannot
        // be merged with another by constant merging or identical code folding,
        // so distinct operation types are guaranteed distinct addresses.
        template <typename Op>
        inline constinit OpInfo op_info{
            std::string_view{op_name<Op>.data(), op_name<Op>.size() - 1}};
    }

    template <typename Op>
    inline constexpr OpId op_id = &detail::op_info<std::remove_cvref_t<Op>>;

    // This is an implementation detail of the tracing framework. This structure
    // represents a tracer, whose type information has been erased, thus
    // allowing us to store heterogeneous tracers in the same container.
    struct TypeErasedTracer
    {
        template <typename R>
            requires(Tracer<R> && !std::is_const_v<std::remove_reference_t<R>>)
        static TypeErasedTracer erase(R &r MONAD_LIFETIMEBOUND)
        {
            return TypeErasedTracer{
                std::addressof(r), &vtable_for<std::remove_cvref_t<R>>};
        }

        bool dispatch(
            OpId const op_type, void const *const op, void *const result) const
        {
            return vtable_->dispatch(self_, op_type, op, result);
        }

        void reset() const
        {
            vtable_->reset(self_);
        }

    private:
        struct VTable
        {
            bool (*dispatch)(void *, OpId, void const *, void *);
            void (*reset)(void *);
        };

        template <typename R>
        static bool dispatch_impl(
            void *const self, OpId const op_type, void const *const raw_op,
            void *const result)
        {
            using Signature = typename R::Signature;
            constexpr size_t num_ops = std::tuple_size_v<Signature>;
            auto *const tracer = static_cast<R *>(self);

            auto dispatch_case = [&]<size_t I>(auto &self_fn) -> bool {
                if constexpr (I == num_ops) {
                    return false;
                }
                else {
                    using Op = std::tuple_element_t<I, Signature>;
                    if (op_type == op_id<Op>) {
                        // TODO(dhil): This assertion is redundant if this
                        // object was applied by the tracing context
                        // object. It would be good to make this
                        // abstraction tighter, so that we know invoking
                        // this case is always well-defined.
                        MONAD_ASSERT_THROW(
                            raw_op, "Raw operation pointer is null");
                        auto const &op = *static_cast<Op const *>(raw_op);

                        if constexpr (std::same_as<return_type_t<Op>, void>) {
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

                    return self_fn.template operator()<I + 1>(self_fn);
                }
            };

            return dispatch_case.template operator()<0>(dispatch_case);
        }

        template <typename R>
        static void reset_impl(void *const self)
        {
            static_cast<R *>(self)->reset();
        }

        template <typename R>
        static constexpr VTable vtable_for{&dispatch_impl<R>, &reset_impl<R>};

        TypeErasedTracer(void *const self, VTable const *const vtable)
            : self_{self}
            , vtable_{vtable}
        {
        }

        void *self_;
        VTable const *vtable_;
    };

    static_assert(sizeof(TypeErasedTracer) == 16);
}

// The tracing context for a single transaction. Its interface offers one
// parametrized method `run` for performing a trace operation, which is then
// dispatched to the first suitable tracer in this context, returning the answer
// if any, and a method `reset` which is broadcast to every tracer in this
// context.
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
            dispatch(trace::op_id<Op>, &op, nullptr);
            return;
        }
        else {
            // Typed fast exit, returning the empty optional.
            if (tracers_.empty()) {
                return std::nullopt;
            }

            Op op(std::forward<Args>(args)...);
            answer_type_t<Op> answer{};
            dispatch(trace::op_id<Op>, &op, &answer);
            return answer;
        }
    }

    // Resets every tracer in this context, discarding any state accumulated by
    // a prior execution attempt of the transaction.
    void reset() const;

    // Returns the number of tracers in this context.
    size_t size() const;

private:
    void dispatch(trace::OpId op_type, void const *op, void *result) const;

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

    template <typename R>
        requires Tracer<R>
    BlockTraceContext &with_system_tracer(R &tracer MONAD_LIFETIMEBOUND)
    {
        using namespace monad::trace;

        if (!!system_call_tracer_) {
            struct SystemCallTracerAlreadyInstalled : public std::exception
            {
                char const *what() const noexcept override
                {
                    return "BlockTraceContext already has a system call tracer "
                           "installed";
                }
            };

            throw SystemCallTracerAlreadyInstalled();
        }
        system_call_tracer_ =
            std::make_unique<TypeErasedTracer>(TypeErasedTracer::erase(tracer));

        return *this;
    }

    // Returns the system call tracing context.
    TxTraceContext system_call_context() const;

    // Returns a tracing context for the ith transaction.
    TxTraceContext slice(size_t i) const;

    // Tests whether the tracing context can be sliced n-ways.
    bool can_slice(size_t n) const;

    // Returns the number of tracers installed per transaction in this context.
    size_t tracers_per_tx() const;

private:
    size_t const num_txs_;
    std::unique_ptr<std::vector<monad::trace::TypeErasedTracer>[]> tracers_;
    std::unique_ptr<monad::trace::TypeErasedTracer> system_call_tracer_;
};

static_assert(sizeof(BlockTraceContext) == 24);

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
