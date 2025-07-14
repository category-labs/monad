#pragma once

#include <atomic>
#include <bit>
#include <cassert>
#include <compare>
#include <cstdint>

#include <linux/types.h> // for __u64

#define MONAD_ASYNC_NAMESPACE_BEGIN                                            \
    namespace monad                                                            \
    {                                                                          \
        namespace async                                                        \
        {

#define MONAD_ASYNC_NAMESPACE_END                                              \
    }                                                                          \
    }

#define MONAD_ASYNC_NAMESPACE ::monad::async

#include <category/core/assert.h>
#include <category/core/hash.hpp>

#ifndef MONAD_CONTEXT_HAVE_ASAN
    #ifndef __clang__
        #if defined(__SANITIZE_ADDRESS__)
            #define MONAD_CONTEXT_HAVE_ASAN 1
        #elif defined(__SANITIZE_THREAD__)
            #define MONAD_CONTEXT_HAVE_TSAN 1
        #elif defined(__SANITIZE_UNDEFINED__)
            #define MONAD_CONTEXT_HAVE_UBSAN 1
        #endif
    #else
        #if __has_feature(address_sanitizer)
            #define MONAD_CONTEXT_HAVE_ASAN 1
        #elif __has_feature(thread_sanitizer)
            #define MONAD_CONTEXT_HAVE_TSAN 1
        #elif defined(__SANITIZE_UNDEFINED__)
            #define MONAD_CONTEXT_HAVE_UBSAN 1
        #endif
    #endif
#endif

MONAD_ASYNC_NAMESPACE_BEGIN

//! The same type io_uring uses for offsets into files during i/o
using file_offset_t = __u64;

//! An identifier of data within a `storage_pool`
struct chunk_offset_t
{
    file_offset_t offset : 28; //!< Offset into the chunk, max is 256Mb
    file_offset_t id : 20; //!< Id of the chunk, max is 1 million, therefore
                           //!< maximum addressable storage is 256Tb

    /*! Next fifteen bits are unused by the async library and can be used by
    client code for anything they wish. Triedb places a
    `node_disk_pages_spare_15` into these bits which it uses to store how
    many 512 byte sectors to read to completely load a node's value, thus both
    a node's location within storage and how many bytes are needed to read it
    are encapsulated within a single dense 64 bit identifier for Triedb.
    */
    file_offset_t spare : 15;
    file_offset_t bits_format : 1; //! Reserve top bit to switch between
                                   //! different bits formatting

    static constexpr file_offset_t max_offset = (1ULL << 28) - 1;
    static constexpr file_offset_t max_id = (1U << 20) - 1;
    static constexpr file_offset_t max_spare = (1ULL << 15) - 1;

    static constexpr chunk_offset_t invalid_value() noexcept
    {
        return {max_id, max_offset};
    }

    constexpr chunk_offset_t(
        uint32_t id_, file_offset_t offset_, file_offset_t spare_ = max_spare)
        : offset(offset_ & max_offset)
        , id(id_ & max_id)
        , spare{spare_ & max_spare}
        , bits_format{0x1}
    {
        MONAD_DEBUG_ASSERT(id_ <= max_id);
        MONAD_DEBUG_ASSERT(offset_ <= max_offset);
        MONAD_DEBUG_ASSERT(spare_ <= max_spare);
    }

    constexpr bool operator==(chunk_offset_t const &o) const noexcept
    {
        return offset == o.offset && id == o.id;
    }

    constexpr auto operator<=>(chunk_offset_t const &o) const noexcept
    {
        if (offset == o.offset && id == o.id) {
            return std::weak_ordering::equivalent;
        }
        if (id < o.id || (id == o.id && offset < o.offset)) {
            return std::weak_ordering::less;
        }
        return std::weak_ordering::greater;
    }

    constexpr chunk_offset_t add_to_offset(file_offset_t offset_) const noexcept
    {
        chunk_offset_t ret(*this);
        offset_ += ret.offset;
        MONAD_DEBUG_ASSERT(offset_ <= max_offset);
        ret.offset = offset_ & max_offset;
        return ret;
    }

    constexpr file_offset_t raw() const noexcept
    {
        union _
        {
            file_offset_t ret;
            chunk_offset_t self;

            constexpr _()
                : ret{}
            {
            }
        } u;

        u.self = *this;
        u.self.spare =
            0; // must be flattened, otherwise can't go into the rbtree key
        u.self.bits_format = 0;
        return u.ret;
    }

    void set_spare(uint16_t value) noexcept
    {
        MONAD_DEBUG_ASSERT(value < max_spare);
        spare = value & max_spare;
    }
};

static_assert(sizeof(chunk_offset_t) == 8);
static_assert(alignof(chunk_offset_t) == 8);
static_assert(std::is_trivially_copyable_v<chunk_offset_t>);

struct chunk_offset_t_hasher
{
    constexpr size_t operator()(chunk_offset_t v) const noexcept
    {
        return fnv1a_hash<file_offset_t>()(v.raw());
    }
};

//! Tag type for tests to ask for anonymous inodes
struct use_anonymous_inode_tag
{
};

//! The invalid file offset
static constexpr chunk_offset_t INVALID_OFFSET =
    chunk_offset_t::invalid_value();

//! The CPU page size and bits to assume
static constexpr uint16_t CPU_PAGE_BITS = 12;
static constexpr uint16_t CPU_PAGE_SIZE = (1U << CPU_PAGE_BITS);

//! The storage i/o page size and bits to assume
static constexpr uint16_t DISK_PAGE_BITS = 9;
static constexpr uint16_t DISK_PAGE_SIZE = (1U << DISK_PAGE_BITS);

//! The DMA friendly page size and bits
static constexpr uint16_t DMA_PAGE_BITS = 6;
static constexpr uint16_t DMA_PAGE_SIZE = (1U << DMA_PAGE_BITS);

MONAD_ASYNC_NAMESPACE_END

namespace std
{
    template <>
    class atomic<MONAD_ASYNC_NAMESPACE::chunk_offset_t>
    {
        atomic<uint64_t> v_;

    public:
        using value_type = MONAD_ASYNC_NAMESPACE::chunk_offset_t;

        constexpr bool is_lock_free() const noexcept
        {
            return v_.is_lock_free();
        }

        constexpr atomic(value_type v) noexcept
            : v_(std::bit_cast<uint64_t>(v))
        {
        }

        atomic(atomic const &) = delete;
        atomic(atomic &&) = delete;
        atomic &operator=(atomic const &) = delete;
        atomic &operator=(atomic &&) = delete;

        void store(
            value_type v,
            std::memory_order ord = std::memory_order_seq_cst) noexcept
        {
            v_.store(std::bit_cast<uint64_t>(v), ord);
        }

        value_type
        load(std::memory_order ord = std::memory_order_seq_cst) const noexcept
        {
            return std::bit_cast<value_type>(v_.load(ord));
        }

        value_type exchange(
            value_type desired,
            std::memory_order ord = std::memory_order_seq_cst) noexcept
        {
            return std::bit_cast<value_type>(
                v_.exchange(std::bit_cast<uint64_t>(desired), ord));
        }
    };
}

static_assert(sizeof(std::atomic<MONAD_ASYNC_NAMESPACE::chunk_offset_t>) == 8);
static_assert(alignof(std::atomic<MONAD_ASYNC_NAMESPACE::chunk_offset_t>) == 8);
static_assert(std::is_trivially_copyable_v<
              std::atomic<MONAD_ASYNC_NAMESPACE::chunk_offset_t>>);
