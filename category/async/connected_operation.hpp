// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/async/detail/connected_operation_storage.hpp>

/* The following Sender-Receiver implementation is loosely based on
https://wg21.link/p2300 `std::execution`. We don't actually
implement P2300 because:

1. It is hard on compile times for the benefits it gives.

2. It is heavy on the templates for the benefits it gives.

3. It suffers from doing too much, but also too little, unsurprising
given its painful gestation through the standards committee where
arguably the committee eventually settled a "best we can do considering"
design.

4. We don't want in any way for our implementation of Senders-Receivers
to ever collide with the standard one, so we are intentionally very
incompatible.



All that said, the Senders-Receivers abstraction is the correct one,
so we employ it here, and if you in the future need to use this code,
it is semantically similar to P2300. To use:

1. Create the Sender for the operation you wish to perform, configured
with the arguments you wish.

2. Create the Receiver for how you would like the operation completion
to be implemented.

3. Connect your Sender and your Receiver into a connected operation
state. This moves your Sender and your Receiver into the operation
state.

4. Submit the connected operation state to AsyncIO, which is taken
by reference. You cannot touch this object in any way after this.
Note that connection operation states cannot be moved nor copied.

5. When the operation completes, its Receiver shall be invoked.

6. You are now allowed to touch the connection operation state. For
most cases, destroying it is the easiest.



If you really care about performance, there is a more awkward to
use option:

1. In your currently not-in-use connected operation state, set
the Sender and Receiver to what you need them to be.

2. Submit the connected operation state to AsyncIO, which is taken
by reference. You cannot touch this object in any way after this.
Note that connection operation states cannot be moved nor copied.

3. When the operation completes, its Receiver shall be invoked.

4. You are now allowed to touch the connection operation state.
You should call `reset()` on it to free any internal resources,
which will also call `reset()` on its sender and receiver.
*/

MONAD_ASYNC_NAMESPACE_BEGIN

//! \brief Concept match of a void taking Sender-Receiver pair
template <typename Sender, typename Receiver>
concept void_taking_sender_receiver_pair =
    sender<Sender> && receiver<Receiver> &&
    ((
         !requires { &Sender::completed; } &&
         requires(Receiver r, erased_connected_operation *o, result<void> res) {
             r.set_value(o, std::move(res));
         }) ||
     requires(
         Sender s, Receiver r, erased_connected_operation *o,
         result<void> res) { r.set_value(o, s.completed(o, std::move(res))); });

//! \brief Concept match of a bytes transferred taking Sender-Receiver pair
template <typename Sender, typename Receiver>
concept size_t_taking_sender_receiver_pair =
    sender<Sender> && receiver<Receiver> &&
    ((
         !requires { &Sender::completed; } &&
         requires(
             Receiver r, erased_connected_operation *o, result<size_t> res) {
             r.set_value(o, std::move(res));
         }) ||
     requires(
         Sender s, Receiver r, erased_connected_operation *o,
         result<size_t> res) {
         r.set_value(o, s.completed(o, std::move(res)));
     });

//! \brief Concept match of a filled read buffer taking Sender-Receiver pair
template <typename Sender, typename Receiver>
concept filled_read_buffer_taking_sender_receiver_pair =
    sender<Sender> && receiver<Receiver> &&
    ((
         !requires { &Sender::completed; } &&
         requires(
             Receiver r, erased_connected_operation *o,
             result<std::reference_wrapper<filled_read_buffer>> res) {
             r.set_value(o, std::move(res));
         }) ||
     requires(
         Sender s, Receiver r, erased_connected_operation *o,
         result<std::reference_wrapper<filled_read_buffer>> res) {
         r.set_value(o, s.completed(o, std::move(res)));
     });

//! \brief Concept match of a filled write buffer taking Sender-Receiver pair
template <typename Sender, typename Receiver>
concept filled_write_buffer_taking_sender_receiver_pair =
    sender<Sender> && receiver<Receiver> &&
    ((
         !requires { &Sender::completed; } &&
         requires(
             Receiver r, erased_connected_operation *o,
             result<std::reference_wrapper<filled_write_buffer>> res) {
             r.set_value(o, std::move(res));
         }) ||
     requires(
         Sender s, Receiver r, erased_connected_operation *o,
         result<std::reference_wrapper<filled_write_buffer>> res) {
         r.set_value(o, s.completed(o, std::move(res)));
     });

namespace detail
{
    template <
        class Base, sender Sender, receiver Receiver,
        bool is_void_taking_sender_receiver_pair =
            void_taking_sender_receiver_pair<Sender, Receiver>,
        bool is_size_t_taking_sender_receiver_pair =
            size_t_taking_sender_receiver_pair<Sender, Receiver>,
        bool is_filled_read_buffer_taking_sender_receiver_pair =
            filled_read_buffer_taking_sender_receiver_pair<Sender, Receiver>,
        bool is_filled_write_buffer_taking_sender_receiver_pair =
            filled_write_buffer_taking_sender_receiver_pair<Sender, Receiver>>
    struct connected_operation_completed_implementation : public Base
    {
        using Base::Base;
        static_assert(
            is_void_taking_sender_receiver_pair +
                    is_size_t_taking_sender_receiver_pair +
                    is_filled_read_buffer_taking_sender_receiver_pair +
                    is_filled_write_buffer_taking_sender_receiver_pair >
                0,
            "If Sender's result_type is not one of: (i) result<void> (ii) "
            "result<size_t> (iii) result<filled_read_buffer> (iv) "
            "result<filled_write_buffer>, it must provide a completed(T) "
            "for one of those types to transform a completion into the "
            "appropriate result_type value for the Receiver.");
        static_assert(
            is_void_taking_sender_receiver_pair +
                    is_size_t_taking_sender_receiver_pair +
                    is_filled_read_buffer_taking_sender_receiver_pair +
                    is_filled_write_buffer_taking_sender_receiver_pair <
                2,
            "Multiple Sender::result_type to Receiver::set_value() paths "
            "detected (possibly via Sender::complete()), it is ambiguous which "
            "is meant.");

    private:
        virtual void completed(result<void>) override final
        {
            abort();
        }

        virtual void completed(result<size_t>) override final
        {
            abort();
        }

        virtual void completed(
            result<std::reference_wrapper<filled_read_buffer>>) override final
        {
            abort();
        }

        virtual void completed(
            result<std::reference_wrapper<filled_write_buffer>>) override final
        {
            abort();
        }
    };

    template <class Base, sender Sender, receiver Receiver>
    struct connected_operation_completed_implementation<
        Base, Sender, Receiver, true, false, false, false> : public Base
    {
        using Base::Base;

        // Overload ambiguity resolver so you can write `completed(success())`
        // without ambiguous overload warnings.
        void completed(BOOST_OUTCOME_V2_NAMESPACE::success_type<void> _)
        {
            completed(result<void>(_));
        }

        // These will devirtualise and usually disappear entirely from codegen
        virtual void completed(result<void> res) override final
        {
            this->completed_impl_(std::move(res));
        }

        virtual void completed(result<size_t> res) override final
        {
            // Decay to the void type
            if (!res) {
                completed(result<void>(std::move(res).as_failure()));
            }
            else {
                completed(result<void>(success()));
            }
        }

        virtual void
        completed(result<std::reference_wrapper<filled_read_buffer>> res)
            override final
        {
            // Decay to the void type
            if (!res) {
                completed(result<void>(std::move(res).as_failure()));
            }
            else {
                completed(result<void>(success()));
            }
        }

        virtual void
        completed(result<std::reference_wrapper<filled_write_buffer>> res)
            override final
        {
            // Decay to the void type
            if (!res) {
                completed(result<void>(std::move(res).as_failure()));
            }
            else {
                completed(result<void>(success()));
            }
        }
    };

    template <class Base, sender Sender, receiver Receiver>
    struct connected_operation_completed_implementation<
        Base, Sender, Receiver, false, true, false, false> : public Base
    {
        using Base::Base;

    private:
        virtual void completed(result<void>) override final
        {
            // If you reach here, somebody called a void completed()
            // on a bytes transferred type connected operation
            abort();
        }

    public:
        // This will devirtualise and usually disappear entirely from codegen
        virtual void completed(result<size_t> bytes_transferred) override final
        {
            this->completed_impl_(std::move(bytes_transferred));
        }

        virtual void
        completed(result<std::reference_wrapper<filled_read_buffer>> res)
            override final
        {
            // Decay to the bytes transferred type
            if (!res) {
                completed(result<size_t>(std::move(res).as_failure()));
            }
            else {
                completed(
                    result<size_t>(success(res.assume_value().get().size())));
            }
        }

        virtual void
        completed(result<std::reference_wrapper<filled_write_buffer>> res)
            override final
        {
            // Decay to the bytes transferred type
            if (!res) {
                completed(result<size_t>(std::move(res).as_failure()));
            }
            else {
                completed(
                    result<size_t>(success(res.assume_value().get().size())));
            }
        }
    };

    template <class Base, sender Sender, receiver Receiver>
    struct connected_operation_completed_implementation<
        Base, Sender, Receiver, false, false, true, false> : public Base
    {
        using Base::Base;

    private:
        // This will devirtualise and usually disappear entirely from codegen
        virtual void completed(result<void>) override final
        {
            // If you reach here, somebody called a void completed()
            // on a filled read buffer type connected operation
            abort();
        }

        virtual void completed(result<size_t>) override final
        {
            // If you reach here, somebody called a bytes transferred
            // completed() on a filled read buffer type connected operation
            abort();
        }

        virtual void completed(
            result<std::reference_wrapper<filled_write_buffer>>) override final
        {
            // If you reach here, somebody called a filled write buffer
            // completed() on a filled read buffer type connected operation
            abort();
        }

    public:
        virtual void
        completed(result<std::reference_wrapper<filled_read_buffer>>
                      read_buffer_filled) override final
        {
            this->completed_impl_(std::move(read_buffer_filled));
        }
    };

    template <class Base, sender Sender, receiver Receiver>
    struct connected_operation_completed_implementation<
        Base, Sender, Receiver, false, false, false, true> : public Base
    {
        using Base::Base;

    private:
        // This will devirtualise and usually disappear entirely from codegen
        virtual void completed(result<void>) override final
        {
            // If you reach here, somebody called a void completed()
            // on a filled write buffer type connected operation
            abort();
        }

        virtual void completed(result<size_t>) override final
        {
            // If you reach here, somebody called a bytes transferred
            // completed() on a filled write buffer type connected operation
            abort();
        }

        virtual void completed(
            result<std::reference_wrapper<filled_read_buffer>>) override final
        {
            // If you reach here, somebody called a filled read buffer
            // completed() on a filled write buffer type connected operation
            abort();
        }

    public:
        virtual void
        completed(result<std::reference_wrapper<filled_write_buffer>>
                      write_buffer_filled) override final
        {
            this->completed_impl_(std::move(write_buffer_filled));
        }
    };
}

/*! \class connected_operation
\brief A connected sender-receiver pair which implements operation state.

The customisation point is the free function `connect()` which may
be overloaded to return an extended `connected_operation` type containing
additional i/o specific state.

`connected_operation` cannot be relocated in memory, and must not be
destructed between submission and completion.

`connected_operation` can be reused if its sender-receiver pair supports
that.
*/
template <sender Sender, receiver Receiver>
class connected_operation final
    : public detail::connected_operation_completed_implementation<
          detail::connected_operation_storage<
              erased_connected_operation, Sender, Receiver>,
          Sender, Receiver>
{
    using base_ = detail::connected_operation_completed_implementation<
        detail::connected_operation_storage<
            erased_connected_operation, Sender, Receiver>,
        Sender, Receiver>;

public:
    using base_::base_;

    // This is an immovable in memory object
    connected_operation(connected_operation const &) = delete;
    connected_operation(connected_operation &&) = delete;
    connected_operation &operator=(connected_operation const &) = delete;
    connected_operation &operator=(connected_operation &&) = delete;
};

//! Default connect customisation point taking sender and receiver by value,
//! requires receiver to be compatible with sender.
template <sender Sender, receiver Receiver>
    requires(compatible_sender_receiver<Sender, Receiver>)
inline connected_operation<Sender, Receiver>
connect(Sender &&sender, Receiver &&receiver)
{
    return connected_operation<Sender, Receiver>(
        static_cast<Sender &&>(sender), static_cast<Receiver &&>(receiver));
}

//! \overload
template <sender Sender, receiver Receiver>
    requires(compatible_sender_receiver<Sender, Receiver>)
inline connected_operation<Sender, Receiver>
connect(AsyncIO &io, Sender &&sender, Receiver &&receiver)
{
    return connected_operation<Sender, Receiver>(
        io, static_cast<Sender &&>(sender), static_cast<Receiver &&>(receiver));
}

//! Alternative connect customisation point taking piecewise construction args,
//! requires receiver to be compatible with sender
template <
    sender Sender, receiver Receiver, class... SenderArgs,
    class... ReceiverArgs>
    requires(
        compatible_sender_receiver<Sender, Receiver> &&
        std::is_constructible_v<Sender, SenderArgs...> &&
        std::is_constructible_v<Receiver, ReceiverArgs...>)
inline connected_operation<Sender, Receiver> connect(
    std::piecewise_construct_t _, std::tuple<SenderArgs...> &&sender_args,
    std::tuple<ReceiverArgs...> &&receiver_args)
{
    return connected_operation<Sender, Receiver>(
        _, std::move(sender_args), std::move(receiver_args));
}

//! \overload
template <
    sender Sender, receiver Receiver, class... SenderArgs,
    class... ReceiverArgs>
    requires(
        compatible_sender_receiver<Sender, Receiver> &&
        std::is_constructible_v<Sender, SenderArgs...> &&
        std::is_constructible_v<Receiver, ReceiverArgs...>)
inline connected_operation<Sender, Receiver> connect(
    AsyncIO &io, std::piecewise_construct_t _,
    std::tuple<SenderArgs...> &&sender_args,
    std::tuple<ReceiverArgs...> &&receiver_args)
{
    return connected_operation<Sender, Receiver>(
        io, _, std::move(sender_args), std::move(receiver_args));
}

MONAD_ASYNC_NAMESPACE_END
