#pragma once

#include <monad/core/assert.h>
#include <monad/core/cmemory.hpp>

#include <concepts>
#include <memory>
#include <span>
#include <stdexcept>

MONAD_NAMESPACE_BEGIN

namespace allocators
{
    namespace detail
    {
        template <class T>
        struct is_unique_ptr : public std::false_type
        {
        };

        template <class T, class Deleter>
        struct is_unique_ptr<std::unique_ptr<T, Deleter>>
            : public std::true_type
        {
        };
    }

    //! \brief Concept matching a STL allocator.
    template <class T>
    concept allocator =
        requires(T a, size_t n) { a.deallocate(a.allocate(n), n); };

    //! \brief Concept matching a Deleter template parameter for a `unique_ptr`.
    template <class T, class U>
    concept unique_ptr_deleter = requires(T x, U *p) { x(p); };

    //! \brief Concept matching a `unique_ptr`.
    template <class T>
    concept unique_ptr = detail::is_unique_ptr<std::decay_t<T>>::value;

    //! \brief If a type opts into this, `calloc_free_allocator` and `calloc` is
    //! used and constructors are NOT called. Only opt into this if your type is
    //! happy seeing all bytes zero as if it had been constructed, this can be a
    //! win for same use cases (`calloc` may be able to avoid zeroing memory if
    //! it knows its source is already zeroed) but can also be a loss if zeroing
    //! bytes is more expensive than calling the constructor.
    //!
    //! \warning Be SURE to specialise this before instantiating any code which
    //! instantiates allocator code! Otherwise it will have no effect.
    template <class T>
    struct construction_equals_all_bits_zero : std::false_type
    {
    };

    //! \brief Injects a noop `construct()` into a STL allocator.
    template <allocator Base>
    struct disable_construct_in_allocator : public Base
    {
        template <class U, class... Args>
        void construct(U *, Args &&...)
        {
        }
    };

    /**************************************************************************/
    //! \brief A STL allocator which uses `malloc`-`free`.
    template <class T>
    struct malloc_free_allocator
    {
        using value_type = T;

        [[nodiscard]] constexpr T *allocate(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(T) > alignof(max_align_t)) {
                return reinterpret_cast<T *>(
                    std::aligned_alloc(alignof(T), no * sizeof(T)));
            }
            return reinterpret_cast<T *>(std::malloc(no * sizeof(T)));
        }

        template <class U>
        [[nodiscard]] constexpr T *allocate_overaligned(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(U) > alignof(max_align_t)) {
                return reinterpret_cast<T *>(
                    std::aligned_alloc(alignof(U), no * sizeof(T)));
            }
            return reinterpret_cast<T *>(std::malloc(no * sizeof(T)));
        }

        constexpr void deallocate(T *const p, size_t const)
        {
            std::free(p);
        }
    };

    //! \brief A STL allocator which uses `calloc`-`free` (i.e. allocated bytes
    //! are returned zeroed)
    template <class T>
    struct calloc_free_allocator
    {
        using value_type = T;

        [[nodiscard]] constexpr T *allocate(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(T) > alignof(max_align_t)) {
                char *ret = reinterpret_cast<char *>(
                    std::aligned_alloc(alignof(T), no * sizeof(T)));
                cmemset(ret, char(0), no * sizeof(T));
                return reinterpret_cast<T *>(ret);
            }
            return reinterpret_cast<T *>(std::calloc(no, sizeof(T)));
        }

        template <class U>
        [[nodiscard]] constexpr T *allocate_overaligned(size_t const no)
        {
            MONAD_ASSERT(no < size_t(-1) / sizeof(T));
            if constexpr (alignof(U) > alignof(max_align_t)) {
                char *ret = reinterpret_cast<char *>(
                    std::aligned_alloc(alignof(U), no * sizeof(T)));
                cmemset(ret, char(0), no * sizeof(T));
                return reinterpret_cast<T *>(ret);
            }
            return reinterpret_cast<T *>(std::calloc(no, sizeof(T)));
        }

        constexpr void deallocate(T *const p, size_t const)
        {
            std::free(p);
        }
    };

    //! \brief Chooses `calloc_free_allocator` if
    //! `construction_equals_all_bits_zero<T>` is true, else
    //! `malloc_free_allocator`
    template <class T, class U = T>
    using calloc_free_allocator_if_opted_in = std::conditional_t<
        construction_equals_all_bits_zero<T>::value, calloc_free_allocator<U>,
        malloc_free_allocator<U>>;

    /**************************************************************************/
    //! \brief A unique ptr deleter for a STL allocator
    template <allocator Alloc, Alloc &(*GetAllocator)()>
    struct unique_ptr_allocator_deleter
    {
        using allocator_type = Alloc;
        using value_type = typename Alloc::value_type;

        constexpr unique_ptr_allocator_deleter() = default;

        constexpr void operator()(value_type *const p) const
        {
            using allocator_traits = std::allocator_traits<allocator_type>;
            Alloc &alloc = GetAllocator();
            allocator_traits::destroy(alloc, p);
            allocator_traits::deallocate(alloc, p, 1);
        }
    };

    namespace detail
    {
        template <allocator TypeAlloc, allocator RawAlloc>
        struct type_raw_alloc_pair
        {
            using type_allocator = TypeAlloc;
            using raw_bytes_allocator = RawAlloc;

            TypeAlloc &type_alloc;
            RawAlloc &raw_alloc;
        };

        template <class T>
        inline type_raw_alloc_pair<
            std::allocator<T>, calloc_free_allocator_if_opted_in<T, std::byte>>
        GetStdAllocatorPair()
        {
            static std::allocator<T> a;
            static calloc_free_allocator_if_opted_in<T, std::byte> b;
            return {a, b};
        }
    }

    //! \brief A unique ptr deleter for a STL allocator where underlying storage
    //! exceeds type
    template <
        allocator TypeAlloc, allocator RawAlloc,
        detail::type_raw_alloc_pair<TypeAlloc, RawAlloc> (*GetAllocator)(),
        size_t (*GetSize)(typename TypeAlloc::value_type *)>
    struct unique_ptr_aliasing_allocator_deleter
    {
        using allocator_type = TypeAlloc;
        using value_type = typename TypeAlloc::value_type;

        constexpr unique_ptr_aliasing_allocator_deleter() {}

        constexpr void operator()(value_type *const p1) const
        {
            using allocator1_traits = std::allocator_traits<allocator_type>;
            using allocator2_traits = std::allocator_traits<RawAlloc>;
            // Use all bits one for the number of items to deallocate in
            // order to trap use of unsuitable user supplied allocators
            using size_type2 = allocator2_traits::size_type;
            auto no = static_cast<size_type2>(-1);
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored                                                 \
    "-Waddress" // warns about GetSize never being null
            if (GetSize != nullptr) {
                no = GetSize(p1);
            }
#pragma GCC diagnostic pop
            auto [alloc1, alloc2] = GetAllocator();
            allocator1_traits::destroy(alloc1, p1);
            auto *p2 = reinterpret_cast<std::byte *>(p1);
            allocator2_traits::deallocate(alloc2, p2, no);
        }
    };

    //! \brief An implementation of proposed `allocate_unique`, a STL allocator
    //! aware `unique_ptr`.
    template <allocator Alloc, Alloc &(*GetAllocator)(), class... Args>
        requires(std::is_constructible_v<typename Alloc::value_type, Args...>)
    inline constexpr std::unique_ptr<
        typename Alloc::value_type,
        unique_ptr_allocator_deleter<Alloc, GetAllocator>>
    allocate_unique(Args &&...args)
    {
        using allocator_traits = std::allocator_traits<Alloc>;
        Alloc &alloc = GetAllocator();
        auto *p = allocator_traits::allocate(alloc, 1);
        try {
            if constexpr (
                sizeof...(args) > 0 || !construction_equals_all_bits_zero<
                                           typename Alloc::value_type>::value) {
                allocator_traits::construct(
                    alloc, p, static_cast<Args &&>(args)...);
            }
            return std::unique_ptr<
                typename Alloc::value_type,
                unique_ptr_allocator_deleter<Alloc, GetAllocator>>(p);
        }
        catch (...) {
            allocator_traits::deallocate(alloc, p, 1);
            throw;
        }
    }

    //! \brief A STL allocator aware unique ptr whose storage is larger than its
    //! type. Useful for variably lengthed types. Needs a raw storage allocator
    //! capable of deallocating without being told how many bytes to deallocate.
    template <
        allocator TypeAlloc, allocator RawAlloc,
        detail::type_raw_alloc_pair<TypeAlloc, RawAlloc> (*GetAllocator)(),
        size_t (*GetSize)(typename TypeAlloc::value_type *) = nullptr,
        class... Args>
        requires(
            std::is_same_v<typename RawAlloc::value_type, std::byte> &&
            std::is_constructible_v<typename TypeAlloc::value_type, Args...>)
    inline constexpr std::unique_ptr<
        typename TypeAlloc::value_type,
        unique_ptr_aliasing_allocator_deleter<
            TypeAlloc, RawAlloc, GetAllocator, GetSize>>
    allocate_aliasing_unique(size_t const storagebytes, Args &&...args)
    {
        MONAD_ASSERT(storagebytes >= sizeof(typename TypeAlloc::value_type));
        using allocator1_traits = std::allocator_traits<TypeAlloc>;
        using allocator2_traits = std::allocator_traits<RawAlloc>;
        auto [alloc1, alloc2] = GetAllocator();
        std::byte *p2;
        if constexpr (
            alignof(typename TypeAlloc::value_type) > alignof(max_align_t)) {
            p2 = alloc2.template allocate_overaligned<
                typename TypeAlloc::value_type>(storagebytes);
        }
        else {
            p2 = allocator2_traits::allocate(alloc2, storagebytes);
        }
#ifndef NDEBUG
        if constexpr (!construction_equals_all_bits_zero<
                          typename TypeAlloc::value_type>::value) {
            // Trap use of region after end of type
            cmemset(p2, std::byte{0xff}, storagebytes);
        }
#endif
        try {
            auto *p1 = reinterpret_cast<typename TypeAlloc::value_type *>(p2);
            if constexpr (
                sizeof...(args) > 0 ||
                !construction_equals_all_bits_zero<
                    typename TypeAlloc::value_type>::value) {
                allocator1_traits::construct(
                    alloc1, p1, static_cast<Args &&>(args)...);
            }
            using deleter_type = unique_ptr_aliasing_allocator_deleter<
                TypeAlloc,
                RawAlloc,
                GetAllocator,
                GetSize>;
            return std::
                unique_ptr<typename TypeAlloc::value_type, deleter_type>(p1);
        }
        catch (...) {
            allocator2_traits::deallocate(alloc2, p2, storagebytes);
            throw;
        }
    }
}

MONAD_NAMESPACE_END
