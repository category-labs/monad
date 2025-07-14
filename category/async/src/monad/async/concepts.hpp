#pragma once

#include "config.hpp"

#include <boost/outcome/experimental/status_result.hpp>
#include <boost/outcome/try.hpp>

// TODO unstable paths between versions
#if __has_include(                                                             \
    <boost/outcome/experimental/status-code/system_code_from_exception.hpp>)
    #include <boost/outcome/experimental/status-code/system_code_from_exception.hpp>
#else
    #include <boost/outcome/experimental/status-code/status-code/system_code_from_exception.hpp>
#endif

#include <type_traits>

MONAD_ASYNC_NAMESPACE_BEGIN

template <class T>
using result = ::boost::outcome_v2::experimental::status_result<T>;
using ::boost::outcome_v2::experimental::errc;
using ::boost::outcome_v2::experimental::failure;
using ::boost::outcome_v2::experimental::posix_code;
using ::boost::outcome_v2::experimental::success;
using ::boost::outcome_v2::experimental::system_code_from_exception;

class erased_connected_operation;

template <class T>
concept sender =
    std::is_destructible_v<T> &&
    std::is_invocable_r_v<result<void>, T, erased_connected_operation *> &&
    requires { typename T::result_type; } &&
    (
        std::is_same_v<typename T::result_type, result<void>> ||
        requires(T s, erased_connected_operation *o, result<void> x) {
            {
                s.completed(o, std::move(x))
            } -> std::same_as<typename T::result_type>;
        } || std::is_same_v<typename T::result_type, result<size_t>> ||
        requires(T s, erased_connected_operation *o, result<size_t> x) {
            {
                s.completed(o, std::move(x))
            } -> std::same_as<typename T::result_type>;
        });

template <class T>
concept receiver = std::is_destructible_v<T>;

template <class Sender, class Receiver>
concept compatible_sender_receiver =
    sender<Sender> && receiver<Receiver> &&
    requires(
        Receiver r, erased_connected_operation *o,
        typename Sender::result_type x) { r.set_value(o, std::move(x)); };

MONAD_ASYNC_NAMESPACE_END
