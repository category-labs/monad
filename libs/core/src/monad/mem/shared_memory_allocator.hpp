#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/mem/treap_allocator.hpp>
#include <monad/synchronization/spin_lock.hpp>

#include <mutex>

MONAD_NAMESPACE_BEGIN

/// Main class
class SharedMemoryAllocator;

/// Helper classes
struct RemotePack;
struct LocalPack;
struct SuperblockDescriptor;
class DescriptorDll;

/// RemotePack is a multi-field 32-bit packed structure that can be accessed
/// atomically. Used to hold the state of a superblock and used for nonlocal
/// deallocation.
struct RemotePack
{
    /* Superblock states:
       0 LOCAL -- local superblock
       1 ALLOCATED -- fully allocated superblock
       2 PARTIAL_TO_LIST -- being pushed in partial list
       3 PARTIAL_IN_LIST -- in partial list
       4 FREE_TO_LIST -- fully free, being pushed in partial list
       5 FREE_IN_LIST -- fully free, in partial list
       6 FREE_REMOVED -- fully free, safe to reclaim or reuse completely
    */
    uint32_t state_ : 3; // superblock state
    uint32_t rcount_ : 11; // number of available blocks in rhead_ list
    uint32_t rhead_ : 11; // sll of deallocated blocks
    uint32_t pad_ : 7;
};

MONAD_NAMESPACE_END

template <>
struct quill::copy_loggable<monad::RemotePack> : std::true_type
{
};

template <>
struct fmt::formatter<monad::RemotePack> : public ::monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::RemotePack const &a, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "{{"
            "{},"
            "{},"
            "{},"
            "{}"
            "}}",
            a.state_,
            a.rcount_,
            a.rhead_,
            a.pad_);
        return ctx.out();
    }
};

MONAD_NAMESPACE_BEGIN

/// LocalPack is a multi-field 32-bit packed structure used by the owner of a
/// local superblock.
struct LocalPack
{
    uint32_t lcount_ : 11; // number of available blocks in lhead_ and unused_
    uint32_t lhead_ : 11; // sll of deallocated blocks
    uint32_t unused_ : 10; // index of first unused block
};

MONAD_NAMESPACE_END

template <>
struct quill::copy_loggable<monad::LocalPack> : std::true_type
{
};

template <>
struct fmt::formatter<monad::LocalPack> : public ::monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::LocalPack const &a, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "{{"
            "{},"
            "{},"
            "{}"
            "}}",
            a.lcount_,
            a.lhead_,
            a.unused_);
        return ctx.out();
    }
};

MONAD_NAMESPACE_BEGIN

struct SuperblockDescriptor
{
    std::atomic<RemotePack> rpack_;
    LocalPack lpack_;
    SuperblockDescriptor *prev_;
    SuperblockDescriptor *next_;
    char pad_[40]; // to reduce false sharing

    RemotePack rpack_load() const
    {
        return rpack_.load(std::memory_order_acquire);
    }

    void rpack_store(RemotePack const newrpack)
    {
        return rpack_.store(newrpack, std::memory_order_release);
    }

    RemotePack rpack_exchange(RemotePack const rpack)
    {
        return rpack_.exchange(rpack, std::memory_order_acq_rel);
    }

    bool rpack_cas(RemotePack &expval, RemotePack const newval)
    {
        return rpack_.compare_exchange_weak(
            expval,
            newval,
            std::memory_order_acq_rel,
            std::memory_order_acquire);
    }
};

/// Lock-protected dll of superblock descriptors
class DescriptorDll
{
    SpinLock lock_;
    SuperblockDescriptor *head_{nullptr};
    SuperblockDescriptor *tail_{nullptr};
    char pad_[40];

public:
    template <class Func>
    void push(SuperblockDescriptor *const desc, Func const fn)
    {
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(head_) & 0x3f) == 0);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(tail_) & 0x3f) == 0);
        MONAD_DEBUG_ASSERT(desc);
        desc->next_ = nullptr;
        std::unique_lock g(lock_);
        if (fn()) {
            if (tail_) {
                desc->prev_ = tail_;
                tail_->next_ = desc;
            }
            else {
                desc->prev_ = nullptr;
                head_ = desc;
            }
            tail_ = desc;
        }
        MONAD_DEBUG_ASSERT(
            (reinterpret_cast<uintptr_t>(desc->prev_) & 0x3f) == 0);
        MONAD_DEBUG_ASSERT(
            (reinterpret_cast<uintptr_t>(desc->next_) & 0x3f) == 0);
    }

    template <class Func>
    SuperblockDescriptor *pop(Func const fn)
    {
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(head_) & 0x3f) == 0);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(tail_) & 0x3f) == 0);
        std::unique_lock g(lock_);
        while (true) {
            SuperblockDescriptor *const desc = head_;
            if (desc) {
                MONAD_DEBUG_ASSERT(desc->prev_ == nullptr);
                MONAD_DEBUG_ASSERT(
                    (reinterpret_cast<uintptr_t>(desc->next_) & 0x3f) == 0);
                auto const next = desc->next_;
                desc->next_ = nullptr;
                head_ = next;
                if (next) {
                    MONAD_DEBUG_ASSERT(next->prev_ = desc);
                    MONAD_DEBUG_ASSERT(tail_ != desc);
                    next->prev_ = nullptr;
                }
                else {
                    MONAD_DEBUG_ASSERT(tail_ == desc);
                    tail_ = nullptr;
                }
                if (!fn(desc)) {
                    continue;
                }
            }
            return desc;
        }
    }

    template <class Func>
    void remove(SuperblockDescriptor *const desc, Func const fn)
    {
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(head_) & 0x3f) == 0);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(tail_) & 0x3f) == 0);
        MONAD_DEBUG_ASSERT(desc);
        MONAD_DEBUG_ASSERT(
            (reinterpret_cast<uintptr_t>(desc->prev_) & 0x3f) == 0);
        MONAD_DEBUG_ASSERT(
            (reinterpret_cast<uintptr_t>(desc->next_) & 0x3f) == 0);
        std::unique_lock g(lock_);
        if (fn()) {
            auto prev = desc->prev_;
            auto next = desc->next_;
            if (prev) {
                desc->prev_ = nullptr;
                MONAD_DEBUG_ASSERT(prev->next_ == desc);
                prev->next_ = next;
            }
            else {
                MONAD_DEBUG_ASSERT(head_ == desc);
                head_ = next;
            }
            if (next) {
                desc->next_ = nullptr;
                MONAD_DEBUG_ASSERT(next->prev_ == desc);
                next->prev_ = prev;
            }
            else {
                MONAD_DEBUG_ASSERT(tail_ == desc);
                tail_ = prev;
            }
        }
    }
};

////////////////////////
/// MAIN ALLOCATOR CLASS
////////////////////////

class SharedMemoryAllocator
{
    using Desc = SuperblockDescriptor;

    struct Sizeclass
    {
        size_t size_; // block size
        uint16_t first_index_; // index of first block in superblock
        uint16_t end_index_; // index of last+1 block in superblock
        uint8_t sb_sc_; // size class of superblock
    };

    // CONSTANTS

    // Offsets
    static constexpr size_t LARGE_OFFSET = 0;
    static constexpr size_t PARTIAL_OFFSET = 1024;
    static constexpr size_t DESC_OFFSET = 4 * 1024;
    // Alignment
    static constexpr size_t SUPERBLOCK_ALIGN = 8 * 1024;
    static constexpr size_t MASK_ALIGN = SUPERBLOCK_ALIGN - 1;
    // Sizes
    static constexpr size_t HYPERBLOCK_SIZE = 1024 * 1024;
    static constexpr size_t HYPERBLOCK_MASK = HYPERBLOCK_SIZE - 1;
    static constexpr uint16_t SB_MAX_BLOCKS = 1024;
    // Masks
    static constexpr uint32_t MASK10 = 0x3ffU;
    static constexpr uint32_t MASK11 = 0x7ffU;
    // States
    static constexpr uint8_t STATE_LOCAL = 0;
    static constexpr uint8_t STATE_ALLOCATED = 1;
    static constexpr uint8_t STATE_PARTIAL_TO_LIST = 2;
    static constexpr uint8_t STATE_PARTIAL_IN_LIST = 3;
    static constexpr uint8_t STATE_FREE_TO_LIST = 4;
    static constexpr uint8_t STATE_FREE_IN_LIST = 5;
    static constexpr uint8_t STATE_FREE_REMOVED = 6;
    // Sizeclass indexes
    static constexpr uint8_t INDEX_1K = 13;
    static constexpr uint8_t INDEX_2K = 14;
    static constexpr uint8_t INDEX_8K = 16;
    static constexpr uint8_t INDEX_64K = 19;
    static constexpr uint8_t INDEX_256K = 21;
    static constexpr uint8_t INDEX_HYPERBLOCK = 23;
    static constexpr uint8_t NUM_SIZECLASSES = 24;
    // Sizeclass constants
    static_assert(sizeof(Desc) == 64);
    static constexpr Sizeclass SIZECLASSES[NUM_SIZECLASSES] = {
        {8, 8, 8 * 1024 / 8, INDEX_8K},
        {16, 4, 8 * 1024 / 16, INDEX_8K},
        {24, 3, 8 * 1024 / 24, INDEX_8K},
        {32, 2, 8 * 1024 / 32, INDEX_8K},
        {48, 2, 8 * 1024 / 48, INDEX_8K},
        {64, 1, 64 * 1024 / 64, INDEX_64K},
        {96, 1, 64 * 1024 / 96, INDEX_64K},
        {128, 1, 64 * 1024 / 128, INDEX_64K},
        {192, 1, 64 * 1024 / 192, INDEX_64K},
        {256, 1, 256 * 1024 / 256, INDEX_256K},
        {384, 1, 256 * 1024 / 384, INDEX_256K},
        {512, 1, 256 * 1024 / 512, INDEX_256K},
        {768, 1, 256 * 1024 / 768, INDEX_256K},
        {1 * 1024, 0, 1024 / 1, INDEX_HYPERBLOCK},
        {2 * 1024, 0, 1024 / 2, INDEX_HYPERBLOCK},
        {4 * 1024, 0, 1024 / 4, INDEX_HYPERBLOCK},
        {8 * 1024, 0, 1024 / 8, INDEX_HYPERBLOCK},
        {16 * 1024, 0, 1024 / 16, INDEX_HYPERBLOCK},
        {32 * 1024, 0, 1024 / 32, INDEX_HYPERBLOCK},
        {64 * 1024, 0, 1024 / 64, INDEX_HYPERBLOCK},
        {128 * 1024, 0, 1024 / 128, INDEX_HYPERBLOCK},
        {256 * 1024, 0, 1024 / 256, INDEX_HYPERBLOCK},
        {512 * 1024, 0, 1024 / 512, INDEX_HYPERBLOCK},
        {HYPERBLOCK_SIZE, 0, INDEX_HYPERBLOCK, 1}};
    // Mapping requested sizes to sizeclasses
    static constexpr uint8_t SC_MAP[129] = {
        0,  0,  1,  2,  3,  4,  4,  5,  5,  6,  6,  6,  6,  7,  7,  7,  7,
        8,  8,  8,  8,  8,  8,  8,  8,  9,  9,  9,  9,  9,  9,  9,  9,  10,
        10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11,
        11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12,
        12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
        12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13,
        13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
        13, 13, 13, 13, 13, 13, 13, 13, 13, 13};

    // STATIC FUNCTIONS

    static_assert(sizeof(TreapAllocator) <= (PARTIAL_OFFSET - LARGE_OFFSET));
    static_assert(
        PARTIAL_OFFSET + NUM_SIZECLASSES * sizeof(DescriptorDll) < DESC_OFFSET);

    // Static
    static constexpr uint8_t find_size_class(size_t const size)
    {
        uint8_t const sc = [size] {
            if (size <= SIZECLASSES[INDEX_1K].size_) {
                MONAD_DEBUG_ASSERT(((size + 7) >> 3) <= 128);
                return SC_MAP[(size + 7) >> 3];
            }
            for (uint8_t i = INDEX_2K; i < NUM_SIZECLASSES; ++i) {
                if (size <= SIZECLASSES[i].size_) {
                    return i;
                }
            }
            return NUM_SIZECLASSES;
        }();
        MONAD_DEBUG_ASSERT(sc <= NUM_SIZECLASSES);
        return sc;
    }

    static constexpr size_t shm_offset(size_t const size, void *const ptr)
    {
        size_t const offset = [size, ptr] {
            size_t const desc_end =
                DESC_OFFSET + sizeof(Desc) * (size / HYPERBLOCK_SIZE);
            size_t const mask = HYPERBLOCK_MASK;
            size_t const trim =
                (reinterpret_cast<uintptr_t>(ptr) + desc_end + mask) & mask;
            return desc_end + (mask - trim);
        }();
        MONAD_DEBUG_ASSERT(
            ((reinterpret_cast<uintptr_t>(ptr) + offset) & HYPERBLOCK_MASK) ==
            0);
        return offset;
    }

    static constexpr size_t block_size(uint8_t const sc)
    {
        return SIZECLASSES[sc].size_;
    }

    static constexpr size_t sb_size(uint8_t const sc)
    {
        return SIZECLASSES[SIZECLASSES[sc].sb_sc_].size_;
    }

    static constexpr uint16_t first_index(uint8_t const sc)
    {
        MONAD_DEBUG_ASSERT(sc < INDEX_HYPERBLOCK);
        uint16_t first = SIZECLASSES[sc].first_index_;
        if (sc >= INDEX_1K) {
            MONAD_DEBUG_ASSERT(first == 0);
        }
        else {
            size_t const block_size = SIZECLASSES[sc].size_;
            (void)block_size;
            MONAD_DEBUG_ASSERT(
                ((sizeof(Desc) + block_size - 1) / block_size) < SB_MAX_BLOCKS);
            MONAD_DEBUG_ASSERT(
                first == ((sizeof(Desc) + block_size - 1) / block_size));
        }
        MONAD_DEBUG_ASSERT(first <= MASK11);
        return MASK11 & first;
    }

    static constexpr uint16_t end_index(uint8_t const sc)
    {
        MONAD_DEBUG_ASSERT(sc < INDEX_HYPERBLOCK);
        MONAD_DEBUG_ASSERT(SIZECLASSES[sc].end_index_ <= SB_MAX_BLOCKS);
        return SIZECLASSES[sc].end_index_;
    }

    static constexpr uint16_t num_blocks(uint8_t const sc)
    {
        return end_index(sc) - first_index(sc);
    }

    static constexpr size_t large_block(size_t const size)
    {
        return (size + HYPERBLOCK_MASK) & ~(HYPERBLOCK_MASK);
    }

    static constexpr TreapAllocator *
    large_allocator(size_t const total_size, void *const ptr, bool const init)
    {
        void *const addr = static_cast<char *>(ptr) + LARGE_OFFSET;
        if (init) {
            size_t const offset = shm_offset(total_size, ptr);
            void *const shm = static_cast<char *>(ptr) + offset;
            return new (addr) TreapAllocator(total_size - offset, shm);
        }
        else {
            return static_cast<TreapAllocator *>(addr);
        }
    }

    static constexpr void
    debug_memset(void *const ptr, int const ch, size_t const size)
    {
#ifdef NDEBUG
        (void)ptr;
        (void)ch;
        (void)size;
#else
        if (size <= 2048) {
            std::memset(ptr, ch, size);
        }
        else {
            std::memset(ptr, ch, 1024);
            std::memset(
                static_cast<void *>(static_cast<char *>(ptr) + size - 1024),
                ch,
                1024);
        }
#endif
    }

    // DATA

    /*
      Shared memory layout:
        large_    Metadata for large block allocator
        partial_  Array of per sizeclass dll-s of partially used superblocks
        desc_     Array of descriptors for 1MB hyperblocks
        shm_      Start of allocatable shared memory
    */
    size_t const total_size_;
    void *const begin_;
    void *const end_;
    TreapAllocator *const large_;
    DescriptorDll *const partial_;
    Desc *const desc_;
    void *const shm_;
    Desc *local_[NUM_SIZECLASSES]{nullptr};

public:
    SharedMemoryAllocator(
        size_t const total_size, // Total size of shared memory
        void *const ptr, // Start of shared memory
        bool const init) // Need to initialize shared memory
        : total_size_(total_size)
        , begin_(ptr)
        , end_(static_cast<char *>(ptr) + total_size)
        , large_(large_allocator(total_size, ptr, init))
        , partial_(static_cast<DescriptorDll *>(
              static_cast<void *>(static_cast<char *>(ptr) + PARTIAL_OFFSET)))
        , desc_(static_cast<Desc *>(
              static_cast<void *>(static_cast<char *>(ptr) + DESC_OFFSET)))
        , shm_(static_cast<char *>(ptr) + shm_offset(total_size, ptr))
    {
        MONAD_DEBUG_ASSERT(total_size > shm_offset(total_size, ptr));
        MONAD_DEBUG_ASSERT(ptr);
        MONAD_DEBUG_ASSERT(
            reinterpret_cast<uintptr_t>(large_) <
            reinterpret_cast<uintptr_t>(partial_));
        MONAD_DEBUG_ASSERT(
            reinterpret_cast<uintptr_t>(partial_) <
            reinterpret_cast<uintptr_t>(desc_));
        MONAD_DEBUG_ASSERT(
            reinterpret_cast<uintptr_t>(desc_) <
            reinterpret_cast<uintptr_t>(shm_));
        MONAD_DEBUG_ASSERT(
            reinterpret_cast<uintptr_t>(large_) -
                reinterpret_cast<uintptr_t>(partial_) >=
            sizeof(TreapAllocator));
        MONAD_DEBUG_ASSERT(
            reinterpret_cast<uintptr_t>(partial_) -
                reinterpret_cast<uintptr_t>(desc_) >=
            NUM_SIZECLASSES * sizeof(DescriptorDll));
        if (init) {
            for (uint8_t i = 0; i < NUM_SIZECLASSES; ++i) {
                new (&partial_[i]) DescriptorDll;
            }
        }
    }

    ~SharedMemoryAllocator()
    {
        clean_up();
    }

    void *alloc(size_t const size)
    {
        uint8_t sc = find_size_class(size);
        void *const ptr = sc < INDEX_HYPERBLOCK
                              ? alloc_sc(sc)
                              : large_->alloc(large_block(size));
        MONAD_DEBUG_ASSERT(ptr);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(ptr) & 7) == 0);
        MONAD_DEBUG_ASSERT(ptr >= shm_);
        MONAD_DEBUG_ASSERT(ptr < end_);
        return ptr;
    }

    void dealloc(void *const ptr, size_t const size)
    {
        uint8_t const sc = find_size_class(size);
        return sc < INDEX_HYPERBLOCK ? dealloc_sc(sc, ptr)
                                     : large_->dealloc(ptr, large_block(size));
    }

private:
    void clean_up()
    {
        for (uint8_t sc = 0; sc < NUM_SIZECLASSES; ++sc) {
            Desc *const local = std::exchange(local_[sc], nullptr);
            if (local) {
                move_local_to_partial(sc, local);
            }
        }
    }

    void move_local_to_partial(uint8_t const sc, Desc *const local)
    {
        while (true) {
            RemotePack rpack = local->rpack_load();
            MONAD_DEBUG_ASSERT(rpack.state_ == STATE_LOCAL);
            RemotePack newrpack = rpack;
            newrpack.state_ = STATE_PARTIAL_TO_LIST;
            if (local->rpack_cas(rpack, newrpack)) {
                push_to_partial_list(sc, local);
                break;
            }
        }
    }

    void push_to_partial_list(uint8_t const sc, Desc *const desc)
    {
        partial_[sc].push(desc, [desc] {
            while (true) {
                RemotePack rpack = desc->rpack_load();
                RemotePack newrpack = rpack;
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_LOCAL);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_ALLOCATED);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_PARTIAL_IN_LIST);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_FREE_IN_LIST);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_FREE_REMOVED);
                if (rpack.state_ == STATE_PARTIAL_TO_LIST) {
                    newrpack.state_ = STATE_PARTIAL_IN_LIST;
                }
                else if (rpack.state_ == STATE_FREE_TO_LIST) {
                    newrpack.state_ = STATE_FREE_REMOVED;
                }
                else {
                    MONAD_DEBUG_ASSERT(false);
                }
                if (desc->rpack_cas(rpack, newrpack)) {
                    return rpack.state_ == STATE_PARTIAL_TO_LIST;
                }
            }
        });
    }

    void *alloc_sc(uint8_t const sc)
    {
        MONAD_DEBUG_ASSERT(sc < INDEX_HYPERBLOCK);
        Desc *&local = local_[sc];
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(local) & 0x3f) == 0);
        if (!local) {
            local = alloc_from_partial(sc);
        }
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(local) & 0x3f) == 0);
        if (!local) {
            local = alloc_new_superblock(sc);
            MONAD_DEBUG_ASSERT(
                (reinterpret_cast<uintptr_t>(local) & 0x3f) == 0);
            make_local_from_new(sc, local);
        }
        return alloc_from_local(sc, local);
    }

    Desc *alloc_new_superblock(uint8_t const sc)
    {
        uint8_t const sb_sc = SIZECLASSES[sc].sb_sc_;
        void *const sb = sb_sc < INDEX_HYPERBLOCK
                             ? alloc_sc(sb_sc)
                             : large_->alloc(HYPERBLOCK_SIZE);
        return sb_to_desc(sc, sb);
    }

    Desc *alloc_from_partial(uint8_t const sc)
    {
        return partial_[sc].pop([](Desc *const desc) {
            while (true) {
                RemotePack rpack = desc->rpack_load();
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_LOCAL);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_ALLOCATED);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_PARTIAL_TO_LIST);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_FREE_TO_LIST);
                MONAD_DEBUG_ASSERT(rpack.state_ != STATE_FREE_REMOVED);
                RemotePack newrpack = rpack;
                if (rpack.state_ == STATE_PARTIAL_IN_LIST) {
                    newrpack.state_ = STATE_LOCAL;
                }
                else if (rpack.state_ == STATE_FREE_IN_LIST) {
                    newrpack.state_ = STATE_FREE_REMOVED;
                }
                else {
                    MONAD_DEBUG_ASSERT(false);
                }
                if (desc->rpack_cas(rpack, newrpack)) {
                    return rpack.state_ == STATE_PARTIAL_IN_LIST;
                }
            }
        });
    }

    void set_lpack_from_rpack(
        uint8_t const sc, LocalPack &lpack, RemotePack const rpack)
    {
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(&lpack) & 0x3f) == 4);
        (void)sc;
        MONAD_DEBUG_ASSERT(rpack.rcount_ > 0);
        MONAD_DEBUG_ASSERT(rpack.rcount_ <= num_blocks(sc));
        MONAD_DEBUG_ASSERT(rpack.rhead_ < end_index(sc));
        MONAD_DEBUG_ASSERT(lpack.lcount_ == 0);
        MONAD_DEBUG_ASSERT(lpack.lhead_ == end_index(sc));

        MONAD_DEBUG_ASSERT(lpack.unused_ == 0);
        lpack.lcount_ = rpack.rcount_;
        lpack.lhead_ = rpack.rhead_;
    }

    void make_local_from_new(uint8_t const sc, Desc *const desc)
    {
        MONAD_DEBUG_ASSERT(desc);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(desc) & 0x3f) == 0);
        desc->rpack_store(
            RemotePack{STATE_LOCAL, 0, end_index(sc) & MASK11, 111});
        desc->lpack_ = LocalPack{
            num_blocks(sc) & MASK11,
            end_index(sc) & MASK11,
            first_index(sc) & MASK10};
    }

    void *alloc_from_local(uint8_t const sc, Desc *&local)
    {
        MONAD_DEBUG_ASSERT(local);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(local) & 0x3f) == 0);
        auto &lpack = local->lpack_;
        MONAD_DEBUG_ASSERT(
            local->rpack_.load(std::memory_order_relaxed).state_ ==
            STATE_LOCAL);
        if (lpack.lcount_ == 0) {
            MONAD_DEBUG_ASSERT(lpack.lhead_ == end_index(sc));
            MONAD_DEBUG_ASSERT(lpack.unused_ == 0);
            RemotePack const rpack = local->rpack_exchange(
                {STATE_LOCAL, 0, end_index(sc) & MASK11, 111});
            MONAD_DEBUG_ASSERT(rpack.state_ == STATE_LOCAL);
            set_lpack_from_rpack(sc, lpack, rpack);
        }
        MONAD_DEBUG_ASSERT(lpack.lcount_ > 0);
        void *const block = alloc_from_lpack(sc, lpack, local);
        if (lpack.lcount_ == 0) {
            try_make_not_local(sc, local);
        }
        return block;
    }

    void *
    alloc_from_lpack(uint8_t const sc, LocalPack &lpack, Desc *const local)
    {
        MONAD_DEBUG_ASSERT(local);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(local) & 0x3f) == 0);
        void *block;
        void *const sb = desc_to_sb(sc, local);
        MONAD_DEBUG_ASSERT((reinterpret_cast<uintptr_t>(sb) & 0x1fff) == 0);
        MONAD_DEBUG_ASSERT(lpack.lhead_ <= end_index(sc));
        if (lpack.lhead_ < end_index(sc)) {
            block = static_cast<char *>(sb) + lpack.lhead_ * block_size(sc);
            MONAD_DEBUG_ASSERT(block >= sb);
            MONAD_DEBUG_ASSERT(
                reinterpret_cast<uintptr_t>(block) <
                (reinterpret_cast<uintptr_t>(sb) + sb_size(sc)));
            uint16_t next = *(reinterpret_cast<uint16_t *>(block));
            MONAD_DEBUG_ASSERT(next >= first_index(sc));
            MONAD_DEBUG_ASSERT(next <= end_index(sc));
            MONAD_DEBUG_ASSERT(lpack.lcount_ > 0);
            --lpack.lcount_;
            lpack.lhead_ = next & MASK11;
        }
        else {
            block = static_cast<char *>(sb) + lpack.unused_ * block_size(sc);
            MONAD_DEBUG_ASSERT(block >= sb);
            MONAD_DEBUG_ASSERT(
                reinterpret_cast<uintptr_t>(block) <
                (reinterpret_cast<uintptr_t>(sb) + sb_size(sc)));
            MONAD_DEBUG_ASSERT(lpack.lcount_ > 0);
            --lpack.lcount_;
            lpack.unused_ = lpack.unused_ < (end_index(sc) - 1)
                                ? (lpack.unused_ + 1) & MASK10
                                : 0;
        }
        return block;
    }

    void try_make_not_local(uint8_t const sc, Desc *&local)
    {
        LocalPack &lpack = local->lpack_;
        (void)lpack;
        (void)sc;
        MONAD_DEBUG_ASSERT(lpack.lcount_ == 0);
        MONAD_DEBUG_ASSERT(lpack.lhead_ == end_index(sc));
        MONAD_DEBUG_ASSERT(lpack.unused_ == 0);
        RemotePack rpack = local->rpack_load();
        if (rpack.rcount_ == 0) {
            MONAD_DEBUG_ASSERT(rpack.rhead_ == end_index(sc));
            RemotePack newrpack = rpack;
            newrpack.state_ = STATE_ALLOCATED;
            if (local->rpack_cas(rpack, newrpack)) {
                local = nullptr;
            }
        }
    }

    void dealloc_sc(uint8_t const sc, void *const ptr)
    {
        MONAD_DEBUG_ASSERT(sc < INDEX_HYPERBLOCK);
        void *const sb = ptr_to_sb(sc, ptr);
        Desc *const desc = sb_to_desc(sc, sb);
        uint16_t const index = ptr_to_index(sc, ptr, sb);
        if (desc == local_[sc]) {
            dealloc_to_local_sb(sc, ptr, index, desc);
        }
        else {
            dealloc_to_remote_sb(sc, ptr, index, desc);
        }
    }

    void dealloc_to_local_sb(
        uint8_t const sc, void *const ptr, uint16_t const index,
        Desc *const desc)
    {
        (void)sc;
        MONAD_DEBUG_ASSERT(index <= MASK10);
        LocalPack &lpack = desc->lpack_;
        if (index + 1 == lpack.unused_) {
            lpack.unused_ = index & MASK10;
        }
        else {
            MONAD_DEBUG_ASSERT(lpack.lhead_ <= end_index(sc));
            *static_cast<uint16_t *>(ptr) = lpack.lhead_;
            lpack.lhead_ = index & MASK10;
        }
        MONAD_DEBUG_ASSERT(lpack.lcount_ < end_index(sc));
        ++lpack.lcount_;
    }

    void dealloc_to_remote_sb(
        uint8_t const sc, void *const ptr, uint16_t const index,
        Desc *const desc)
    {
        MONAD_DEBUG_ASSERT(index <= MASK10);
        while (true) {
            RemotePack rpack = desc->rpack_load();
            MONAD_DEBUG_ASSERT(rpack.rcount_ < num_blocks(sc));
            MONAD_DEBUG_ASSERT(rpack.rhead_ <= end_index(sc));
            *reinterpret_cast<uint16_t *>(ptr) = rpack.rhead_;
            RemotePack newrpack = rpack;
            MONAD_DEBUG_ASSERT(rpack.state_ != STATE_FREE_TO_LIST);
            MONAD_DEBUG_ASSERT(rpack.state_ != STATE_FREE_IN_LIST);
            MONAD_DEBUG_ASSERT(rpack.state_ != STATE_FREE_REMOVED);
            if (rpack.state_ != STATE_LOCAL) {
                if (rpack.state_ == STATE_ALLOCATED) {
                    MONAD_DEBUG_ASSERT(num_blocks(sc) > 1);
                    MONAD_DEBUG_ASSERT(rpack.rcount_ == 0);
                    MONAD_DEBUG_ASSERT(rpack.rhead_ == end_index(sc));
                    newrpack.state_ = STATE_PARTIAL_TO_LIST;
                }
                else if (rpack.rcount_ == num_blocks(sc) - 1) {
                    if (rpack.state_ == STATE_PARTIAL_TO_LIST) {
                        newrpack.state_ = STATE_FREE_TO_LIST;
                    }
                    else if (rpack.state_ == STATE_PARTIAL_IN_LIST) {
                        newrpack.state_ = STATE_FREE_IN_LIST;
                    }
                    else {
                        MONAD_DEBUG_ASSERT(false);
                    }
                }
            }
            ++newrpack.rcount_;
            newrpack.rhead_ = index & MASK10;
            if (desc->rpack_cas(rpack, newrpack)) {
                if (rpack.state_ != STATE_LOCAL) {
                    if (rpack.state_ == STATE_ALLOCATED) {
                        push_to_partial_list(sc, desc);
                    }
                    else if (rpack.rcount_ == num_blocks(sc) - 1) {
                        dealloc_sb(sc, desc);
                    }
                }
                return;
            }
        }
    }

    void dealloc_sb(uint8_t const sc, Desc *const desc)
    {
        while (true) {
            RemotePack rpack = desc->rpack_load();
            if (rpack.state_ == STATE_FREE_IN_LIST) {
                partial_[sc].remove(desc, [desc] {
                    return desc->rpack_load().state_ == STATE_FREE_IN_LIST;
                });
                break;
            }
            else if (rpack.state_ == STATE_FREE_REMOVED) {
                break;
            }
            MONAD_DEBUG_ASSERT(rpack.state_ == STATE_FREE_TO_LIST);
            std::this_thread::yield();
        }
        void *const sb = desc_to_sb(sc, desc);
        debug_memset(sb, 0xbbu, sb_size(sc));
        dealloc(sb, sb_size(sc));
    }

    // Mapping functions

    void *ptr_to_sb(uint8_t sc, void *const ptr)
    {
        MONAD_DEBUG_ASSERT(ptr >= shm_);
        MONAD_DEBUG_ASSERT(
            ptr < static_cast<char *>(shm_) + total_size_ -
                      shm_offset(total_size_, large_));
        MONAD_DEBUG_ASSERT(sc < INDEX_HYPERBLOCK);
        size_t const offset = static_cast<size_t>(
            static_cast<char *>(ptr) - static_cast<char *>(shm_));
        return static_cast<char *>(ptr) - (offset % sb_size(sc));
    }

    uint16_t ptr_to_index(uint8_t const sc, void *const ptr, void *const sb)
    {
        size_t const offset = static_cast<size_t>(
            static_cast<char *>(ptr) - static_cast<char *>(sb));
        MONAD_DEBUG_ASSERT(offset % block_size(sc) == 0);
        MONAD_DEBUG_ASSERT(offset / block_size(sc) <= MASK10);
        return (offset / block_size(sc)) & MASK10;
    }

    Desc *sb_to_desc(uint8_t const sc, void *const sb) const
    {
        uintptr_t const isb = reinterpret_cast<uintptr_t>(sb);
        MONAD_DEBUG_ASSERT((isb & MASK_ALIGN) == 0);
        uintptr_t const ishm = reinterpret_cast<uintptr_t>(shm_);
        MONAD_DEBUG_ASSERT(isb >= ishm);
        if (sc < INDEX_1K) {
            return reinterpret_cast<Desc *>(sb);
        }
        else {
            return &desc_[(isb - ishm) / HYPERBLOCK_SIZE];
        }
    }

    void *desc_to_sb(uint8_t const sc, Desc *const desc) const
    {
        if (sc < INDEX_1K) {
            return static_cast<void *>(desc);
        }
        else {
            return static_cast<void *>(
                static_cast<char *>(shm_) +
                static_cast<size_t>(desc - desc_) * HYPERBLOCK_SIZE);
        }
    }
}; // SharedMemoryAllocator

MONAD_NAMESPACE_END
