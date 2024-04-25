#pragma once

#include <monad/core/assert.h>
#include <monad/core/tl_tid.h>
#include <monad/mem/spinlock.h>

#include <stddef.h>
#include <stdint.h>

static size_t const PAGE_SIZE = 8 * 1024; // 8 KB page
static size_t const ALIGN = 16; // 4 bits

/*utility function*/
static uintptr_t
upper_mask(uintptr_t const addr, uint64_t const alignment, size_t const offset);

struct page_t
{
    page_t *next_; ///< next page in the list
    page_t *prev_; ///< prev page in the list
    uintptr_t free_block_; ///< blocks free list
    size_t offset_;
    size_t n_blocks_allocated_;
    size_t block_size_;
    spin_lock lock_;
};

void init_page(page_t *const page, size_t const block_size)
{
    page->next_ = page->prev_ = nullptr;
    page->free_block_ = (uintptr_t) nullptr;
    page->offset_ = upper_mask((uintptr_t)(page), ALIGN, sizeof(page_t)) -
                    (uintptr_t)(page);
    page->block_size_ = block_size;
    page->n_blocks_allocated_ = 0;
}

bool try_lock_page(page_t *const page)
{
    return try_lock(&page->lock_);
}

void lock_page(page_t *const page)
{
    lock(&page->lock_);
}

void unlock_page(page_t *const page)
{
    unlock(&page->lock_);
}

// requires lock

bool is_empty(page_t const *const page)
{
    MONAD_DEBUG_ASSERT(page->lock_.lock_ == get_tl_tid());
    return page->n_blocks_allocated_ == 0;
}

bool is_full(page_t const *const page)
{
    MONAD_DEBUG_ASSERT(page->lock_.lock_ == get_tl_tid());
    if (page->free_block_ == (uintptr_t) nullptr &&
        page->offset_ + page->block_size_ > PAGE_SIZE) {
        return true;
    }
    return false;
}

void *alloc_block(page_t *const page)
{
    MONAD_DEBUG_ASSERT(page->lock_.lock_ == get_tl_tid());
    void *ret_addr = nullptr;
    if (page->free_block_ != (uintptr_t) nullptr) { // use free list
        ret_addr = (void *)(page->free_block_);
        // delete block from free list
        page->free_block_ = (uintptr_t)(*(char **)(page->free_block_));
    }
    else { // use offset
        ret_addr = (void *)((uintptr_t)page + page->offset_);
        page->offset_ += (page->block_size_);
    }
    page->n_blocks_allocated_++;
    return ret_addr;
}

void dealloc_block(page_t *const page, void const *const addr)
{
    MONAD_DEBUG_ASSERT(page->lock_.lock_ == get_tl_tid());
    *(char **)addr = (char *)(page->free_block_);
    page->free_block_ = (uintptr_t)addr;
    page->n_blocks_allocated_--;
}

static uintptr_t upper_mask(
    uintptr_t const addr, uint64_t const alignment, size_t const offset = 0)
{
    uintptr_t lower_mask = ~(alignment - 1);
    return (lower_mask & (addr + offset - 1)) + alignment;
}
