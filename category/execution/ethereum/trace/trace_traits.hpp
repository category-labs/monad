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

#include <category/core/config.hpp>

#include <concepts>
#include <functional>
#include <optional>
#include <span>
#include <tuple>
#include <type_traits>
#include <typeindex>

MONAD_NAMESPACE_BEGIN

template <typename... Ts>
using Signature = std::tuple<Ts...>;

// Type-checking machinery
template <typename R>
concept CheckSignature =
    requires { typename std::remove_cvref_t<R>::Signature; };

template <typename R>
struct HasSignature
{
    static constexpr bool has_signature = CheckSignature<R>;

    static consteval bool check()
    {
        // TODO(dhil): Tweak the error message.
        static_assert(
            has_signature,
            "Runner must define 'using Signature = Signature<...>;' to conform "
            "with the structure of a runner");
        return has_signature;
    }
};

template <typename R, typename Op>
concept HandlesOp = requires(std::remove_cvref_t<R> &runner, Op const &op) {
    { std::invoke(runner, op) } -> std::same_as<void>;
};

template <typename R, typename Signature>
struct HandleOpsImpl;

template <typename R, typename... Ops>
struct HandleOpsImpl<R, Signature<Ops...>>
{
    static constexpr bool handle_ops = (HandlesOp<R, Ops> && ...);
};

template <typename R>
struct HandleOps
{
    static constexpr bool handle_ops = HandleOpsImpl<
        R, typename std::remove_cvref_t<R>::Signature>::handle_ops;

    static consteval bool check()
    {
        static_assert(
            handle_ops,
            "Runner must implement a `void operator()(Op const&)` "
            "for every operation type in the Signature");
        return handle_ops;
    }
};

template <typename R>
concept Runner = HasSignature<R>::check() && HandleOps<R>::check();

// TODO(dhil): Clean up the return type computing machinery.

template <typename Op, typename = void>
struct full_answer_type
{
    using type = void;
};

template <typename Op>
struct full_answer_type<Op, std::void_t<typename Op::return_type>>
{
    using type = std::optional<typename Op::return_type>;
};

template <typename Op, typename = void>
struct answer_type
{
    using return_type = void;
    using full_answer_type = typename full_answer_type<Op>::type;
};

template <typename Op>
struct answer_type<Op, std::void_t<typename Op::return_type>>
{
    using return_type = typename Op::return_type;
    using full_answer_type = typename full_answer_type<Op>::type;
};

template <typename Op>
using return_type_t = typename answer_type<Op>::return_type;
template <typename Op>
using answer_type_t = typename answer_type<Op>::full_answer_type;

MONAD_NAMESPACE_END
