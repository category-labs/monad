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

#include <category/async/concepts.hpp>
#include <category/async/erased_connected_operation.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/nested_status_code.hpp>)
    #include <boost/outcome/experimental/status-code/nested_status_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/status-code/nested_status_code.hpp>
#endif

#include <variant>
#include <vector>

MONAD_ASYNC_NAMESPACE_BEGIN

// helper custom status code for Sender `completed()`
enum class sender_errc : uint8_t
{
    unknown = 0,
    operation_must_be_reinitiated, //!< Don't invoke the receiver, instead
                                   //!< reinitiate the operation
    initiation_immediately_completed //!< Returned during initiation to say the
                                     //!< operation was able to complete
                                     //!< immediately
};

MONAD_ASYNC_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<MONAD_ASYNC_NAMESPACE::sender_errc>
    : quick_status_code_from_enum_defaults<MONAD_ASYNC_NAMESPACE::sender_errc>
{
    static constexpr auto const domain_name = "sender_errc domain";

    static constexpr auto const domain_uuid =
        "{18e7ec45-c9b8-58b8-6506-9380542f219d}";

    static std::initializer_list<mapping> const &value_mappings()
    {
        static std::initializer_list<mapping> const v = {
            {MONAD_ASYNC_NAMESPACE::sender_errc::operation_must_be_reinitiated,
             "operation_must_be_reinitiated",
             {}},
            {MONAD_ASYNC_NAMESPACE::sender_errc::
                 initiation_immediately_completed,
             "initiation_immediately_completed",
             {}},
            {MONAD_ASYNC_NAMESPACE::sender_errc::unknown, "unknown", {}},
        };
        return v;
    }
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END

MONAD_ASYNC_NAMESPACE_BEGIN

class sender_errc_with_payload_code_domain_;
using sender_errc_with_payload_code =
    BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<
        sender_errc_with_payload_code_domain_>;

class sender_errc_with_payload_code_domain_
    : public BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain
{
    friend sender_errc_with_payload_code;
    template <class StatusCode, class Allocator>
    friend class BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::detail::
        indirecting_domain;
    using base_ = BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code_domain;

public:
    struct value_type
    {
        sender_errc code{sender_errc::unknown};
        std::variant<
            std::monostate, size_t, std::reference_wrapper<filled_read_buffer>,
            std::reference_wrapper<filled_write_buffer>>
            payload;

        constexpr value_type() noexcept {}

        constexpr value_type(sender_errc code_) noexcept
            : code(code_)
        {
        }

        constexpr value_type(
            sender_errc code_, size_t bytes_transferred) noexcept
            : code(code_)
            , payload(bytes_transferred)
        {
        }

        constexpr value_type(
            sender_errc code_,
            std::reference_wrapper<filled_read_buffer> buffer_read) noexcept
            : code(code_)
            , payload(buffer_read)
        {
        }

        constexpr value_type(
            sender_errc code_,
            std::reference_wrapper<filled_write_buffer> buffer_written) noexcept
            : code(code_)
            , payload(buffer_written)
        {
        }
    };

    using base_::string_ref;

    constexpr explicit sender_errc_with_payload_code_domain_(
        typename base_::unique_id_type id = 0xa88a5a64a7d218d8) noexcept
        : base_(id)
    {
    }

    sender_errc_with_payload_code_domain_(
        sender_errc_with_payload_code_domain_ const &) = default;
    sender_errc_with_payload_code_domain_(
        sender_errc_with_payload_code_domain_ &&) = default;
    sender_errc_with_payload_code_domain_ &
    operator=(sender_errc_with_payload_code_domain_ const &) = default;
    sender_errc_with_payload_code_domain_ &
    operator=(sender_errc_with_payload_code_domain_ &&) = default;
    ~sender_errc_with_payload_code_domain_() = default;

    static inline constexpr sender_errc_with_payload_code_domain_ const &get();

    virtual string_ref name() const noexcept override
    {
        return string_ref("sender_errc domain");
    }

#if BOOST_OUTCOME_VERSION_MAJOR > 2 ||                                         \
    (BOOST_OUTCOME_VERSION_MAJOR == 2 && BOOST_OUTCOME_VERSION_MINOR > 2) ||   \
    (BOOST_OUTCOME_VERSION_MAJOR == 2 && BOOST_OUTCOME_VERSION_MAJOR == 2 &&   \
     BOOST_OUTCOME_VERSION_PATCH > 2)
    virtual base_::payload_info_t payload_info() const noexcept override
    {
        return {
            sizeof(value_type),
            sizeof(status_code_domain *) + sizeof(value_type),
            (alignof(value_type) > alignof(status_code_domain *))
                ? alignof(value_type)
                : alignof(status_code_domain *)};
    }
#endif

protected:
    virtual bool _do_failure(
        const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> &code)
        const noexcept override
    {
        (void)code;
        MONAD_ASSERT(code.domain() == *this);
        return true;
    }

    virtual bool _do_equivalent(
        const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> &code1,
        const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> &code2)
        const noexcept override
    {
        MONAD_ASSERT(code1.domain() == *this);
        auto const &c1 =
            static_cast<sender_errc_with_payload_code const &>(code1);
        if (code2.domain() == *this) {
            auto const &c2 =
                static_cast<sender_errc_with_payload_code const &>(code2);
            return c1.value().code == c2.value().code;
        }
        if (code2.domain() ==
            BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
                quick_status_code_from_enum_domain<sender_errc>) {
            auto const &c2 = static_cast<
                BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
                    quick_status_code_from_enum_code<sender_errc> const &>(
                code2);
            return c1.value().code == c2.value();
        }
        return false;
    }

    virtual BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::generic_code _generic_code(
        const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> &code)
        const noexcept override
    {
        (void)code;
        MONAD_ASSERT(code.domain() == *this);
        return errc::unknown;
    }

    virtual string_ref _do_message(
        const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> &code)
        const noexcept override
    {
        MONAD_ASSERT(code.domain() == *this);
        auto const &c =
            static_cast<sender_errc_with_payload_code const &>(code);
        switch (sender_errc(c.value().code)) {
        case sender_errc::initiation_immediately_completed:
            return string_ref("initiation_immediately_completed");
        case sender_errc::operation_must_be_reinitiated:
            return string_ref("operation_must_be_reinitiated");
        case sender_errc::unknown:
            break;
        }
        return string_ref("unknown");
    }

    BOOST_OUTCOME_SYSTEM_ERROR2_NORETURN virtual void _do_throw_exception(
        const BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_code<void> &code)
        const override
    {
        MONAD_ASSERT(code.domain() == *this);
        auto const &c =
            static_cast<sender_errc_with_payload_code const &>(code);
        throw BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::status_error<
            sender_errc_with_payload_code_domain_>(c);
    }
};

constexpr sender_errc_with_payload_code_domain_
    sender_errc_with_payload_code_domain;

inline constexpr sender_errc_with_payload_code_domain_ const &
sender_errc_with_payload_code_domain_::get()
{
    return sender_errc_with_payload_code_domain;
}

namespace detail
{
    extern inline __attribute__((visibility("default"))) auto &
    thread_local_sender_errc_with_payload_code_storage()
    {
        static thread_local struct
            thread_local_sender_errc_with_payload_code_storage_t
        {
            std::atomic<unsigned> in_use{false};
            std::vector<std::byte> allocation;
        } v;

        return v;
    }

    template <class T>
    struct thread_local_sender_errc_with_payload_code_allocator
    {
        using value_type = T;
        using size_type = size_t;
        using difference_type = ptrdiff_t;

        thread_local_sender_errc_with_payload_code_allocator() = default;

        template <class U>
        constexpr thread_local_sender_errc_with_payload_code_allocator(
            thread_local_sender_errc_with_payload_code_allocator<U> const &)
        {
        }

        [[nodiscard]] value_type *allocate(size_type n)
        {
            auto &tls = thread_local_sender_errc_with_payload_code_storage();
            if (!tls.in_use.exchange(true, std::memory_order_acq_rel)) {
                MONAD_ASSERT(size_type(-1) / sizeof(value_type) >= n);
                tls.allocation.resize(n * sizeof(value_type));
                return reinterpret_cast<value_type *>(tls.allocation.data());
            }
            return std::allocator<value_type>().allocate(n);
        }

        void deallocate(value_type *p, size_type n)
        {
            auto &tls = thread_local_sender_errc_with_payload_code_storage();
            if (tls.in_use.load(std::memory_order_acquire) &&
                reinterpret_cast<value_type *>(tls.allocation.data()) == p) {
                tls.in_use.store(false, std::memory_order_release);
                return;
            }
            std::allocator<value_type>().deallocate(p, n);
        }
    };
}

inline auto make_status_code(sender_errc c, size_t bytes_transferred)
{
    return BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::make_nested_status_code<
        sender_errc_with_payload_code>(
        sender_errc_with_payload_code(
            sender_errc_with_payload_code_domain_::value_type{
                c, bytes_transferred}),
        detail::thread_local_sender_errc_with_payload_code_allocator<
            sender_errc_with_payload_code>());
}

using nested_sender_errc_with_payload_code =
    decltype(make_status_code(sender_errc::operation_must_be_reinitiated, 0));

static_assert(
    sizeof(nested_sender_errc_with_payload_code) <=
        sizeof(result<void>::error_type),
    "nested_sender_errc_with_payload_code will not fit inside a "
    "result<void>::error_type!");

inline nested_sender_errc_with_payload_code make_status_code(
    sender_errc c, std::reference_wrapper<filled_read_buffer> buffer_read)
{
    return BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::make_nested_status_code<
        sender_errc_with_payload_code>(
        sender_errc_with_payload_code(
            sender_errc_with_payload_code_domain_::value_type{c, buffer_read}),
        detail::thread_local_sender_errc_with_payload_code_allocator<
            sender_errc_with_payload_code>());
}

inline nested_sender_errc_with_payload_code make_status_code(
    sender_errc c, std::reference_wrapper<filled_write_buffer> buffer_written)
{
    return BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::make_nested_status_code<
        sender_errc_with_payload_code>(
        sender_errc_with_payload_code(
            sender_errc_with_payload_code_domain_::value_type{
                c, buffer_written}),
        detail::thread_local_sender_errc_with_payload_code_allocator<
            sender_errc_with_payload_code>());
}

// ADL discovered customisation point, opts into being able to directly use the
// enum when comparing to status codes.
inline constexpr BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE::
    quick_status_code_from_enum_code<sender_errc>
    make_status_code(sender_errc c)
{
    /* We have to special case this non-payload carrying form to use an extra
    special lightweight status code as the i/o worker pool infrastructure relies
    heavily on the non-payload form of this to be fast.
    */
    return c;
}

MONAD_ASYNC_NAMESPACE_END
