#pragma once

#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/sender_errc.hpp>
#include <monad/core/tl_tid.h>

#include <memory>

MONAD_ASYNC_NAMESPACE_BEGIN

namespace detail
{
    struct AsyncIO_per_thread_state_t
    {
        AsyncIO *instance{nullptr};
        int within_completions_count{0};

        struct
        {
            erased_connected_operation *first{nullptr}, *last{nullptr};
        } pending_initiations;

        struct within_completions_holder;
        within_completions_holder enter_completions();

        bool empty() const noexcept
        {
            return pending_initiations.first == nullptr;
        }

        bool am_within_completions() const noexcept
        {
            MONAD_DEBUG_ASSERT(within_completions_count >= 0);
            return within_completions_count > 0;
        }

        bool if_within_completions_add_to_pending_initiations(
            erased_connected_operation *op)
        {
            erased_connected_operation::rbtree_node_traits::set_parent(
                op,
                nullptr); // use parent to store pointer to next item
            if (!am_within_completions()) {
                within_completions_reached_zero();
                return false;
            }
            if (pending_initiations.first == nullptr) {
                pending_initiations.first = pending_initiations.last = op;
                return true;
            }
            erased_connected_operation::rbtree_node_traits::set_parent(
                pending_initiations.last, op); // use parent to store pointer to
                                               // next item
            pending_initiations.last = op;
            return true;
        }

        void within_completions_reached_zero()
        {
            if (pending_initiations.first != nullptr) {
                within_completions_count++;
                auto *original_last = pending_initiations.last;
                while (pending_initiations.first != nullptr) {
                    erased_connected_operation *op = pending_initiations.first;
                    pending_initiations.first =
                        erased_connected_operation::rbtree_node_traits::
                            get_parent(pending_initiations.first);
                    if (pending_initiations.first == nullptr) {
                        pending_initiations.last = nullptr;
                    }
                    op->do_possibly_deferred_initiate_(true, false);
                    if (op == original_last) {
                        // Prevent infinite loops caused by initiations adding
                        // more stuff to pending initiations
                        break;
                    }
                }
                within_completions_count--;
            }
        }
    };

    // Implemented in io.cpp
    extern __attribute__((visibility("default"))) AsyncIO_per_thread_state_t &
    AsyncIO_per_thread_state();

    inline AsyncIO *AsyncIO_thread_instance() noexcept
    {
        auto &ts = AsyncIO_per_thread_state();
        return ts.instance;
    }

    // Deduce what kind of connected operation we are
    template <sender Sender>
    inline constexpr operation_type sender_operation_type = []() constexpr {
        if constexpr (requires { Sender::my_operation_type; }) {
            return Sender::my_operation_type;
        }
        else {
            return operation_type::unknown;
        }
    }();

    /* Deduce what lifetime managed internally ought to be
       If set by the receiver, AsyncIO cleans these up after completion
       if a read or write op. Otherwise operator delete is called.
    */
    template <sender Sender, receiver Receiver>
    inline constexpr bool lifetime_managed_internally_default = []() constexpr {
        if constexpr (requires { Receiver::lifetime_managed_internally; }) {
            return Receiver::lifetime_managed_internally;
        }
        else {
            /* Default is true if the op is read or write as AsyncIO
            manages those. Otherwise false.
            */
            return sender_operation_type<Sender> == operation_type::read ||
                   sender_operation_type<Sender> == operation_type::write;
        }
    }();

    template <class Base, sender Sender, receiver Receiver>
    struct connected_operation_storage : public Base
    {
        friend class AsyncIO;

    public:
        using initiation_result = typename Base::initiation_result;
        using sender_type = Sender;
        using receiver_type = Receiver;

    protected:
        Sender sender_;
        Receiver receiver_;

        virtual initiation_result do_possibly_deferred_initiate_(
            bool never_defer, bool is_retry) noexcept override
        {
            (void)
                is_retry; // useful to know how this initiation is coming about
            // You must initiate operations on the same kernel thread as
            // the AsyncIO instance associated with this operation state
            // (except for threadsafeop)
            MONAD_DEBUG_ASSERT(
                this->executor() == nullptr || this->is_threadsafeop() ||
                this->executor()->owning_thread_id() == get_tl_tid());
            this->being_executed_ = true;
            // Prevent compiler reordering write of being_executed_ after this
            // point without using actual atomics.
            std::atomic_signal_fence(std::memory_order_release);
            auto *thisio = this->io_.load(std::memory_order_acquire);
            if (!never_defer &&
                AsyncIO_per_thread_state()
                    .if_within_completions_add_to_pending_initiations(this)) {
                return initiation_result::deferred;
            }
            auto r = sender_(this);
            if (!r) {
                this->being_executed_ = false;
                static constexpr auto initiation_immediately_completed =
                    make_status_code(MONAD_ASYNC_NAMESPACE::sender_errc::
                                         initiation_immediately_completed);
                if (r.assume_error() == initiation_immediately_completed) {
                    [[likely]] if (
                        r.assume_error().domain() ==
                        BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
                            quick_status_code_from_enum_domain<sender_errc>) {
                        this->completed(success());
                    }
                    else {
                        nested_sender_errc_with_payload_code sec(
                            std::move(r).assume_error());
                        std::visit(
                            [&](auto &v) {
                                using type = std::decay_t<decltype(v)>;
                                if constexpr (std::is_same_v<
                                                  type,
                                                  std::monostate>) {
                                    this->completed(success());
                                }
                                else {
                                    this->completed(v);
                                }
                            },
                            sec.value()->value().payload);
                    }
                    return initiation_result::initiation_immediately_completed;
                }
                else {
                    this->completed(std::move(r));
                    return initiation_result::initiation_failed_told_receiver;
                }
            }
            if (thisio != nullptr) {
                thisio->notify_operation_initiation_success_(this);
            }
            return initiation_result::initiation_success;
        }

        template <class ResultType>
        void completed_impl_(ResultType res)
        {
            this->being_executed_ = false;
            auto *thisio = this->executor();
            if (thisio != nullptr) {
                thisio->notify_operation_completed_(this, res);
            }
            if constexpr (requires(Sender x) {
                              x.completed(this, std::move(res));
                          }) {
                auto r = this->sender_.completed(this, std::move(res));
                [[unlikely]] if (
                    !r && r.assume_error() ==
                              sender_errc::operation_must_be_reinitiated) {
                    // Completions are allowed to be triggered from threads
                    // different to initiation, but if completion then
                    // reinitiates, this operation state needs a new owner
                    this->io_.store(
                        detail::AsyncIO_thread_instance(),
                        std::memory_order_release);
                    // Also, it is permitted for the completion to completely
                    // replace the operation state with a brand new type with
                    // new vptr, so we must also launder this else the old vptr
                    // will get used on some compilers (currently only clang)
                    std::launder(this)->initiate();
                }
                else {
                    this->receiver_.set_value(this, std::move(r));
                }
            }
            else {
                this->receiver_.set_value(this, std::move(res));
            }
        }

    public:
        connected_operation_storage() = default;

        connected_operation_storage(
            sender_type &&sender, receiver_type &&receiver)
            : erased_connected_operation(
                  sender_operation_type<Sender>,
                  lifetime_managed_internally_default<Sender, Receiver>)
            , sender_(static_cast<Sender &&>(sender))
            , receiver_(static_cast<Receiver &&>(receiver))
        {
        }

        connected_operation_storage(
            AsyncIO &io, sender_type &&sender, receiver_type &&receiver)
            : erased_connected_operation(
                  sender_operation_type<Sender>, io,
                  lifetime_managed_internally_default<Sender, Receiver>)
            , sender_(static_cast<Sender &&>(sender))
            , receiver_(static_cast<Receiver &&>(receiver))
        {
        }

        template <class... SenderArgs, class... ReceiverArgs>
        connected_operation_storage(
            std::piecewise_construct_t, std::tuple<SenderArgs...> sender_args,
            std::tuple<ReceiverArgs...> receiver_args)
            : erased_connected_operation(
                  sender_operation_type<Sender>,
                  lifetime_managed_internally_default<Sender, Receiver>)
            , sender_(std::make_from_tuple<Sender>(std::move(sender_args)))
            , receiver_(
                  std::make_from_tuple<Receiver>(std::move(receiver_args)))
        {
        }

        template <class... SenderArgs, class... ReceiverArgs>
        connected_operation_storage(
            AsyncIO &io, std::piecewise_construct_t,
            std::tuple<SenderArgs...> sender_args,
            std::tuple<ReceiverArgs...> receiver_args)
            : erased_connected_operation(
                  sender_operation_type<Sender>, io,
                  lifetime_managed_internally_default<Sender, Receiver>)
            , sender_(std::make_from_tuple<Sender>(std::move(sender_args)))
            , receiver_(
                  std::make_from_tuple<Receiver>(std::move(receiver_args)))
        {
        }

        connected_operation_storage(connected_operation_storage const &) =
            delete;
        connected_operation_storage(connected_operation_storage &&) = delete;
        connected_operation_storage &
        operator=(connected_operation_storage const &) = delete;
        connected_operation_storage &
        operator=(connected_operation_storage &&) = delete;
        ~connected_operation_storage() = default;

        sender_type &sender() & noexcept
        {
            return sender_;
        }

        sender_type const &sender() const & noexcept
        {
            return sender_;
        }

        sender_type sender() && noexcept
        {
            return static_cast<sender_type &&>(sender_);
        }

        sender_type const sender() const && noexcept
        {
            return static_cast<sender_type &&>(sender_);
        }

        receiver_type const &receiver() const & noexcept
        {
            return receiver_;
        }

        receiver_type &receiver() & noexcept
        {
            return receiver_;
        }

        receiver_type receiver() && noexcept
        {
            return static_cast<receiver_type &&>(receiver_);
        }

        receiver_type const receiver() const && noexcept
        {
            return static_cast<receiver_type const &&>(receiver_);
        }

        static constexpr bool is_unknown_operation_type() noexcept
        {
            return sender_operation_type<Sender> == operation_type::unknown;
        }

        static constexpr bool is_read() noexcept
        {
            return sender_operation_type<Sender> == operation_type::read;
        }

        static constexpr bool is_read_scatter() noexcept
        {
            return sender_operation_type<Sender> ==
                   operation_type::read_scatter;
        }

        static constexpr bool is_write() noexcept
        {
            return sender_operation_type<Sender> == operation_type::write;
        }

        static constexpr bool is_timeout() noexcept
        {
            return sender_operation_type<Sender> == operation_type::timeout;
        }

        static constexpr bool is_threadsafeop() noexcept
        {
            return sender_operation_type<Sender> ==
                   operation_type::threadsafeop;
        }

        //! Initiates the operation, calling the Receiver with any failure,
        //! returning if deferred or if immediate failure occurred.
        //! If successful do NOT modify anything after
        //! this until after completion, it may cause a silent page
        //! copy-on-write.
        initiation_result initiate() noexcept
        {
            // NOTE Keep this in sync with the one in
            // erased_connected_operation. This is here to aid devirtualisation.
            //
            // It is safe to not defer write op, because no write receivers do
            // recursion in current use cases thus no risk of stack exhaustion.
            // The threadsafe op is special, it isn't for this AsyncIO
            // instance and therefore never needs deferring
            return this->do_possibly_deferred_initiate_(
                detail::sender_operation_type<sender_type> ==
                        operation_type::write ||
                    this->is_threadsafeop(),
                false);
        }

        //! Resets the operation state. Only available if both sender and
        //! receiver implement `reset()`
        template <class... SenderArgs, class... ReceiverArgs>
            requires(requires(
                Sender s, Receiver r, SenderArgs... sargs,
                ReceiverArgs... rargs) {
                s.reset(std::forward<decltype(sargs)>(sargs)...);
                r.reset(std::forward<decltype(rargs)>(rargs)...);
            })
        void reset(
            std::tuple<SenderArgs...> sender_args,
            std::tuple<ReceiverArgs...> receiver_args)
        {
            MONAD_ASSERT(!this->being_executed_);
            erased_connected_operation::reset();
            std::apply(
                [this]<typename... Ts>(Ts &&...args) {
                    sender_.reset(std::forward<Ts>(args)...);
                },
                std::move(sender_args));
            std::apply(
                [this]<typename... Ts>(Ts &&...args) {
                    receiver_.reset(std::forward<Ts>(args)...);
                },
                std::move(receiver_args));
            auto *thisio = this->executor();
            if (thisio != nullptr) {
                thisio->notify_operation_reset_(this);
            }
        }
    };
}

MONAD_ASYNC_NAMESPACE_END
