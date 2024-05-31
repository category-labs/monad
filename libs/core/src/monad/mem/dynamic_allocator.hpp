#pragma once

#include <monad/config.hpp>

#include <cassert>
#include <cstdint>
#include <cstdlib>

MONAD_NAMESPACE_BEGIN

/**
 * Class performs allocation, deallocation, and related functionality replacing
 * malloc library.
 */
template <
    unsigned MIN_BITS, unsigned MAX_BITS, unsigned ALIGN_BITS = 4,
    unsigned PAGE_BITS = 16>
class DynamicAllocator
{
    static_assert(PAGE_BITS > MAX_BITS);
    static_assert(MAX_BITS >= MIN_BITS);
    static_assert(MIN_BITS >= ALIGN_BITS);

    struct page_t
    {
        page_t *next_; ///< next page in the list
        page_t *prev_; ///< prev page in the list
        uintptr_t free_block_; ///< blocks free list
        size_t offset_;
        size_t n_blocks_allocated_;
        size_t block_size_;
    };

    static constexpr size_t MIN_SIZE = 1 << MIN_BITS;
    static constexpr size_t MAX_SIZE = 1 << MAX_BITS;
    static constexpr size_t ALIGN = 1 << ALIGN_BITS;
    static constexpr size_t PAGE = 1 << PAGE_BITS;
    static constexpr size_t N_SLOTS = (MAX_SIZE - MIN_SIZE + ALIGN - 1) / ALIGN;
    static constexpr size_t PAGE_LOWER_MASK = ~(PAGE - 1);

    page_t *pages_[N_SLOTS]; ///< array of lists of non-full pages by alloc_size
                             ///< (start of the memory)
    page_t *empty_pages_; ///< list of empty pages
    uintptr_t mem_start_;
    size_t size_; ///< size of memory

    static size_t size_to_slot(size_t const size)
    {
        return (size < MIN_SIZE) ? 0 : (size - MIN_SIZE + ALIGN - 1) / ALIGN;
    }

    static size_t slot_to_size(size_t const slot_num)
    {
        return slot_num * ALIGN + MIN_SIZE;
    }

    static uintptr_t upper_mask(
        uintptr_t const addr, uint64_t const alignment, size_t const offset = 0)
    {
        uintptr_t lower_mask = ~(alignment - 1);
        return (lower_mask & (addr + offset - 1)) + alignment;
    }

    static bool page_full(page_t const *page)
    {
        if (page->free_block_ == reinterpret_cast<uintptr_t>(nullptr) &&
            page->offset_ + page->block_size_ > PAGE) {
            return true;
        }
        return false;
    }

public:
    DynamicAllocator(char *const mem, size_t size)
        : size_(size)
    {
        // initialize pages array
        for (size_t i = 0; i < N_SLOTS; i++) {
            pages_[i] = nullptr;
        }
        char *p = reinterpret_cast<char *>(upper_mask(
            reinterpret_cast<uintptr_t>(mem),
            PAGE,
            0)); // start of pages memory
        mem_start_ = reinterpret_cast<uintptr_t>(p);

        new (p)
            page_t{nullptr, nullptr, uintptr_t(nullptr), sizeof(page_t), 0, 0};

        size_t n_total_pages = (size - ((uintptr_t)p - (uintptr_t)mem)) / PAGE;
        for (size_t i = 0; i < n_total_pages - 1; i++) {
            char *q = p;
            p += PAGE;
            page_t *page = reinterpret_cast<page_t *>(p);
            page->prev_ = nullptr;
            *reinterpret_cast<char **>(p) = q;
        }
        empty_pages_ = reinterpret_cast<page_t *>(p);
    }

    void *alloc(size_t const);
    bool dealloc(void *const);
};

/**
 * Allocates a chunk of memory. Uses custom allocation if size is within
 * operation limits. Finds a corresponding page list and allocates a block
 * from it.
 *
 * @param size Size of memory
 * @return address
 */
template <
    unsigned MIN_ALLOC_BITS, unsigned MAX_ALLOC_BITS, unsigned ALLIGN_BITS,
    unsigned PAGE_BITS>
void *
DynamicAllocator<MIN_ALLOC_BITS, MAX_ALLOC_BITS, ALLIGN_BITS, PAGE_BITS>::alloc(
    size_t const size)
{
    // check if size is within operation limits
    if (size > MAX_SIZE) {
        return nullptr;
    }
    size_t const slot_num = size_to_slot(size);
    if (pages_[slot_num] == nullptr) {
        if (empty_pages_ == nullptr) { // run out of pages
            return nullptr;
        }
        pages_[slot_num] = empty_pages_;
        empty_pages_ = empty_pages_->next_;
        pages_[slot_num]->offset_ =
            upper_mask(
                reinterpret_cast<uintptr_t>(pages_[slot_num]),
                ALIGN,
                sizeof(page_t)) -
            reinterpret_cast<uintptr_t>(pages_[slot_num]);
        pages_[slot_num]->next_ = nullptr;
        pages_[slot_num]->prev_ = nullptr;
        pages_[slot_num]->block_size_ = slot_to_size(slot_num);
        pages_[slot_num]->n_blocks_allocated_ = 0;
        pages_[slot_num]->free_block_ = reinterpret_cast<uintptr_t>(nullptr);
    }

    // store return address
    void *ret_addr = nullptr;
    if (pages_[slot_num]->offset_ + pages_[slot_num]->block_size_ >
        PAGE) { // use free list
        ret_addr = reinterpret_cast<void *>(pages_[slot_num]->free_block_);
        // delete block from free list
        pages_[slot_num]->free_block_ = reinterpret_cast<uintptr_t>(
            *reinterpret_cast<char **>(pages_[slot_num]->free_block_));
    }
    else { // use offset
        ret_addr =
            (void *)((uintptr_t)pages_[slot_num] + pages_[slot_num]->offset_);
        pages_[slot_num]->offset_ += (pages_[slot_num]->block_size_);
    }
    pages_[slot_num]->n_blocks_allocated_++;

    if (page_full(pages_[slot_num])) {
        pages_[slot_num] = pages_[slot_num]->next_;
    }
    return ret_addr;
}

/**
 * Deallocate block of memory from given address. Assumes full block
 * deallocation.
 *
 * @param addr start address
 */
template <
    unsigned MIN_ALLOC_BITS, unsigned MAX_ALLOC_BITS, unsigned ALLIGN_BITS,
    unsigned PAGE_BITS>
bool DynamicAllocator<MIN_ALLOC_BITS, MAX_ALLOC_BITS, ALLIGN_BITS, PAGE_BITS>::
    dealloc(void *const addr)
{
    // find corresponding page
    uintptr_t base_addr = reinterpret_cast<uintptr_t>(addr) & PAGE_LOWER_MASK;

    if (base_addr < mem_start_ || base_addr + PAGE > mem_start_ + size_) {
        return false;
    }

    page_t *page = reinterpret_cast<page_t *>(base_addr);

    // we will need this info later:
    bool is_full = page_full(page);

    // add freed block to the page's free list
    *reinterpret_cast<char **>(addr) =
        reinterpret_cast<char *>(page->free_block_);
    page->free_block_ = reinterpret_cast<uintptr_t>(addr);
    page->n_blocks_allocated_--;

    // make page available if it was full right before
    if (is_full) {
        page->next_ = pages_[size_to_slot(page->block_size_)];
        if (pages_[size_to_slot(page->block_size_)] != nullptr) {
            pages_[size_to_slot(page->block_size_)]->prev_ = page;
        }
        pages_[size_to_slot(page->block_size_)] = page;
        page->prev_ = nullptr;
    }

    // if page is empty, deallocate it
    if (page->n_blocks_allocated_ == 0) {
        if (pages_[size_to_slot(page->block_size_)] ==
            page) { // page was the first element in pages_[...]
            pages_[size_to_slot(page->block_size_)] = page->next_;
            if (page->next_ != nullptr) {
                page->next_->prev_ = nullptr;
            }
        }
        else {
            assert(page->prev_->next_ == page);
            page->prev_->next_ = page->next_;
            if (page->next_ != nullptr) {
                page->next_->prev_ = page->prev_;
            }
        }
        // reinit page
        page->next_ = empty_pages_;
        page->prev_ = nullptr;
        empty_pages_ = page;
    }
    return true;
}

MONAD_NAMESPACE_END
