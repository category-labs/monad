#pragma once

#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
extern "C"
{
    #define SORTED_RING_BUFFER_CXX_INITIALISER                                 \
        {                                                                      \
        }
#else
    #define SORTED_RING_BUFFER_CXX_INITIALISER
#endif

#define SORTED_RING_BUFFER_TYPE(T) struct sorted_ring_buffer_##T

#define SORTED_RING_BUFFER_DECLARE2(tag, T)                                    \
    SORTED_RING_BUFFER_TYPE(tag)                                               \
    {                                                                          \
        int (*const compare)(void const *a, void const *b)                     \
            SORTED_RING_BUFFER_CXX_INITIALISER;                                \
        size_t capacity SORTED_RING_BUFFER_CXX_INITIALISER,                    \
            size SORTED_RING_BUFFER_CXX_INITIALISER,                           \
            index SORTED_RING_BUFFER_CXX_INITIALISER;                          \
        T *storage SORTED_RING_BUFFER_CXX_INITIALISER;                         \
    };
#define SORTED_RING_BUFFER_DECLARE(T)                                          \
    SORTED_RING_BUFFER_DECLARE2(T, T)                                          \
    static inline int sorted_ring_buffer_compare_##T(                          \
        const void *a, const void *b)                                          \
    {                                                                          \
        const __typeof__(((const T *)a)->key) key_a = ((const T *)a)->key;     \
        const __typeof__(((const T *)b)->key) key_b = ((const T *)b)->key;     \
        return (key_a == key_b) ? 0 : ((key_a < key_b) ? -1 : 1);              \
    }

SORTED_RING_BUFFER_DECLARE2(internal_type_erased_impl, void)

//! \brief Return an initialised `SORTED_RING_BUFFER_TYPE(T)`
#define SORTED_RING_BUFFER_INIT(T, initial_capacity)                           \
    {.compare = sorted_ring_buffer_compare_##T,                                \
     .capacity = (initial_capacity),                                           \
     .size = 0,                                                                \
     .index = 0,                                                               \
     .storage =                                                                \
         (T *)aligned_alloc(alignof(T), sizeof(T) * (initial_capacity))};

//! \brief Destroy an initialised `SORTED_RING_BUFFER_TYPE(T)`
#define SORTED_RING_BUFFER_DESTROY(head)                                       \
    if ((head).storage != nullptr) {                                           \
        free((head).storage);                                                  \
        (head).storage = nullptr;                                              \
    }

//! \brief Return the number of items in a `SORTED_RING_BUFFER_TYPE(T)`.
//! Constant time complexity.
#define SORTED_RING_BUFFER_SIZE(head) (head).size

//! \brief True if a `SORTED_RING_BUFFER_TYPE(T)` is empty.  Constant time
//! complexity.
#define SORTED_RING_BUFFER_EMPTY(head) ((head).size == 0)

//! \brief Return the storage capacity of a `SORTED_RING_BUFFER_TYPE(T)`.
//! Constant time complexity.
#define SORTED_RING_BUFFER_CAPACITY(head) (head).capacity

//! \brief Clear a `SORTED_RING_BUFFER_TYPE(T)`. Constant time complexity.
#define SORTED_RING_BUFFER_CLEAR(head)                                         \
    {                                                                          \
        (head).size = 0;                                                       \
        (head).index = 0;                                                      \
    }

//! \brief Return a pointer to the topmost item in a
//! `SORTED_RING_BUFFER_TYPE(T)`, if there is one. Constant time complexity.
#define SORTED_RING_BUFFER_FRONT(head)                                         \
    ({                                                                         \
        __typeof__((head).storage) ret = nullptr;                              \
        if ((head).size > 0) {                                                 \
            ret = &(head).storage[(head).index];                               \
        }                                                                      \
        ret;                                                                   \
    })

//! \brief Remove the topmost item from a `SORTED_RING_BUFFER_TYPE(T)`,
//! returning it by value. If there are no items, you get back an all bits zero
//! `T`. Constant time complexity.
#define SORTED_RING_BUFFER_POP_FRONT(head)                                     \
    ({                                                                         \
        __typeof__(*(head).storage) ret;                                       \
        if ((head).size > 0) {                                                 \
            memcpy(&ret, &(head).storage[(head).index], sizeof(ret));          \
            /*memset(&(head).storage[(head).index], 0, sizeof(ret));*/         \
            if (++(head).index >= (head).capacity) {                           \
                (head).index = 0;                                              \
            }                                                                  \
            (head).size--;                                                     \
        }                                                                      \
        else {                                                                 \
            memset(&ret, 0, sizeof(ret));                                      \
        }                                                                      \
        ret;                                                                   \
    })

#define SORTED_RING_BUFFER_CHECK(head)                                         \
    if (SORTED_RING_BUFFER_SIZE(head) > 1) {                                   \
        for (size_t n = 0; n < SORTED_RING_BUFFER_SIZE(head) - 1; n++) {       \
            size_t idx1 = (head).index + n, idx2 = (head).index + n + 1;       \
            if (idx1 >= (head).capacity) {                                     \
                idx1 -= (head).capacity;                                       \
            }                                                                  \
            if (idx2 >= (head).capacity) {                                     \
                idx2 -= (head).capacity;                                       \
            }                                                                  \
            const __typeof__((head).storage[idx1].key)                         \
                key_a = (head).storage[idx1].key,                              \
                key_b = (head).storage[idx2].key;                              \
            if (key_a > key_b) {                                               \
                printf("%zu. %u\n", n, key_a);                                 \
                printf("%zu. %u\n", n + 1, key_b);                             \
            }                                                                  \
            assert(key_a <= key_b);                                            \
        }                                                                      \
    }

#ifndef NDEBUG
    #define SORTED_RING_BUFFER_CHECK_IF_NDEBUG(head)                           \
        SORTED_RING_BUFFER_CHECK(head)
#else
    #define SORTED_RING_BUFFER_CHECK_IF_NDEBUG(head)
#endif

static inline void *sorted_ring_buffer_get_impl(
    const struct sorted_ring_buffer_internal_type_erased_impl *head, size_t idx,
    size_t const sizeof_)
{
    if (idx >= head->size) {
        return nullptr;
    }
    idx += head->index;
    if (idx >= head->capacity) {
        idx -= head->capacity;
    }
    return (char *)head->storage + idx * sizeof_;
}

static inline __attribute__((warn_unused_result)) bool
sorted_ring_buffer_insert_impl(
    struct sorted_ring_buffer_internal_type_erased_impl *head, void const *item,
    bool expand_capacity_if_needed, size_t const sizeof_, size_t const alignof_)
{
    if (head->size == head->capacity) {
        if (!expand_capacity_if_needed) {
            return false;
        }
        char *newmem =
            (char *)aligned_alloc(alignof_, sizeof_ * head->capacity * 2);
        if (newmem == nullptr) {
            return false;
        }
        size_t const tocopy = head->capacity - head->index;
        memcpy(
            newmem + head->index * sizeof_,
            (char const *)head->storage + head->index * sizeof_,
            tocopy * sizeof_);
        if (tocopy < head->size) {
            memcpy(
                newmem + (head->index + tocopy) * sizeof_,
                head->storage,
                (head->size - tocopy) * sizeof_);
        }
        free(head->storage);
        head->storage = (void *)newmem;
        head->capacity *= 2;
    }
    if (head->size == 0) {
        head->index = 0;
        memcpy(head->storage, item, sizeof_);
        head->size++;
        return true;
    }
    size_t sidx = 0, eidx = head->size - 1;
    for (;;) {
        assert(eidx >= sidx);
        size_t idx = (sidx + eidx) / 2;
        void *i = sorted_ring_buffer_get_impl(head, idx, sizeof_);
        int const cmp = head->compare(item, i);
        if (cmp == 0 || (cmp < 0 && idx == 0) || sidx == eidx) {
            // Preserve stability of insertion
            void *i2 = i;
            bool insert_here = false;
            if (cmp <= 0) {
                insert_here = true;
            }
            else if (cmp > 0 && idx != head->size - 1) {
                idx++;
            }
            for (;;) {
                if (!insert_here) {
                    i = i2;
                    i2 = sorted_ring_buffer_get_impl(head, idx + 1, sizeof_);
                    if (i2 == nullptr || head->compare(i, i2) < 0) {
                        // idx + 1 is where to insert
                        idx++;
                        i2 = (void *)((char *)i + sizeof_);
                        insert_here = true;
                    }
                }
                if (insert_here) {
                    void *const end_of_capacity =
                        (void *)((char *)head->storage +
                                 head->capacity * sizeof_);
                    if (idx < head->size / 2) {
                        // We shall shuffle the front half upwards
                        if (head->index == 0 && idx == 0) {
                            head->index = head->capacity - 1;
                            i2 = (void *)((char *)end_of_capacity - sizeof_);
                        }
                        else if (head->index == 0) {
                            // Move item top of capacity to bottom
                            memcpy(
                                (char *)head->storage +
                                    (head->capacity - 1) * sizeof_,
                                head->storage,
                                sizeof_);
                            // Shuffle bottom of storage up by one
                            size_t const tocopy = idx;
                            memmove(
                                head->storage,
                                (char const *)head->storage + sizeof_,
                                tocopy * sizeof_);
                            head->index = head->capacity - 1;
                            i2 = (void *)((char *)i2 - sizeof_);
                        }
                        else if (i2 == head->storage) {
                            // Shuffle top of storage up by one
                            size_t tocopy = head->capacity - head->index;
                            memmove(
                                (char *)head->storage +
                                    (head->index - 1) * sizeof_,
                                (char *)head->storage + head->index * sizeof_,
                                tocopy * sizeof_);
                            head->index--;
                            i2 = (void *)((char *)end_of_capacity - sizeof_);
                        }
                        else if (
                            head->index + idx >=
                            head->capacity // inserting within values wrapping
                                           // bottom of storage
                        ) {
                            // Shuffle top of storage up by one
                            size_t tocopy = head->capacity - head->index;
                            memmove(
                                (char *)head->storage +
                                    (head->index - 1) * sizeof_,
                                (char *)head->storage + head->index * sizeof_,
                                tocopy * sizeof_);
                            // Move item top of capacity to bottom
                            memcpy(
                                (char *)head->storage +
                                    (head->capacity - 1) * sizeof_,
                                head->storage,
                                sizeof_);
                            // Shuffle bottom of storage up by one
                            tocopy = idx - tocopy;
                            memmove(
                                head->storage,
                                (char const *)head->storage + sizeof_,
                                tocopy * sizeof_);
                            head->index--;
                            i2 = (void *)((char *)i2 - sizeof_);
                        }
                        else {
                            memmove(
                                (char *)head->storage +
                                    (head->index - 1) * sizeof_,
                                (char *)head->storage + head->index * sizeof_,
                                idx * sizeof_);
                            head->index--;
                            i2 = (void *)((char *)i2 - sizeof_);
                        }
                    }
                    else {
                        if (i2 >= end_of_capacity) {
                            i2 = (void *)head->storage;
                        }
                        // We shall shuffle the latter half downwards
                        if (head->index + idx <
                                head->capacity // inserting within top of
                                               // storage
                            &&
                            head->index + head->size >=
                                head->capacity // values wrap off end of storage
                        ) {
                            // Shuffle top of storage down by one
                            size_t tocopy =
                                head->size - (head->capacity - head->index);
                            memmove(
                                (char *)head->storage + sizeof_,
                                head->storage,
                                tocopy * sizeof_);
                            // Move item bottom of capacity to top
                            memcpy(
                                head->storage,
                                (char const *)head->storage +
                                    (head->capacity - 1) * sizeof_,
                                sizeof_);
                            // Shuffle remainder down by one
                            tocopy = head->capacity - head->index - idx - 1;
                            memmove((char *)i2 + sizeof_, i2, tocopy * sizeof_);
                        }
                        else {
                            size_t const tocopy = head->size - idx;
                            memmove((char *)i2 + sizeof_, i2, tocopy * sizeof_);
                        }
                    }
                    memcpy(i2, item, sizeof_);
                    head->size++;
                    return true;
                }
                idx++;
            }
        }
        else if (cmp < 0) {
            eidx = idx;
        }
        else {
            sidx = idx + 1;
        }
    }
}

//! \brief Insert a new item into a `SORTED_RING_BUFFER_TYPE(T)`, returning
//! false if unsuccessful. Complexity is `O(N)` if capacity expansion is not
//! needed.
#define SORTED_RING_BUFFER_INSERT(head, item, expand_capacity_if_needed)       \
    sorted_ring_buffer_insert_impl(                                            \
        (struct sorted_ring_buffer_internal_type_erased_impl *)&(head),        \
        (const void *)&(item),                                                 \
        (expand_capacity_if_needed),                                           \
        sizeof(*(head).storage),                                               \
        alignof(__typeof__(*(head).storage)))

//! \brief Find an existing item in a `SORTED_RING_BUFFER_TYPE(T)`, returning
//! nullptr if unsuccessful. Complexity is `O(log N)`.
#define SORTED_RING_BUFFER_FIND(head, item)                                    \
    ({                                                                         \
        __typeof__((head).storage) ret = nullptr;                              \
        if ((head).size > 0) {                                                 \
            size_t sidx = 0, eidx = (head).size - 1;                           \
            for (;;) {                                                         \
                assert(eidx >= sidx);                                          \
                size_t idx = (sidx + eidx) / 2;                                \
                __typeof__((head).storage) i =                                 \
                    (const __typeof__((head).storage))                         \
                        sorted_ring_buffer_get_impl(                           \
                            (void *)&(head), idx, sizeof(*(head).storage));    \
                int const cmp = ((item).key == i->key)                         \
                                    ? 0                                        \
                                    : (((item).key < i->key) ? -1 : 1);        \
                if (cmp == 0 || (cmp < 0 && idx == 0) || sidx == eidx) {       \
                    if (0 == memcmp(&(item), i, sizeof(item))) {               \
                        ret = i;                                               \
                        goto done;                                             \
                    }                                                          \
                    if (idx > 0) {                                             \
                        size_t idx2 = idx;                                     \
                        do {                                                   \
                            idx2--;                                            \
                            __typeof__((head).storage) i2 =                    \
                                (const __typeof__((head).storage))             \
                                    sorted_ring_buffer_get_impl(               \
                                        (void *)&(head),                       \
                                        idx2,                                  \
                                        sizeof(*(head).storage));              \
                            int const cmp2 =                                   \
                                ((item).key == i2->key)                        \
                                    ? 0                                        \
                                    : (((item).key < i2->key) ? -1 : 1);       \
                            if (cmp2 != 0) {                                   \
                                break;                                         \
                            }                                                  \
                            if (0 == memcmp(&(item), i2, sizeof(item))) {      \
                                ret = i2;                                      \
                                goto done;                                     \
                            }                                                  \
                        }                                                      \
                        while (idx2 > 0);                                      \
                    }                                                          \
                    if (idx < (head).size - 1) {                               \
                        size_t idx2 = idx;                                     \
                        do {                                                   \
                            idx2++;                                            \
                            __typeof__((head).storage) i2 =                    \
                                (const __typeof__((head).storage))             \
                                    sorted_ring_buffer_get_impl(               \
                                        (void *)&(head),                       \
                                        idx2,                                  \
                                        sizeof(*(head).storage));              \
                            int const cmp2 =                                   \
                                ((item).key == i2->key)                        \
                                    ? 0                                        \
                                    : (((item).key < i2->key) ? -1 : 1);       \
                            if (cmp2 != 0) {                                   \
                                break;                                         \
                            }                                                  \
                            if (0 == memcmp(&(item), i2, sizeof(item))) {      \
                                ret = i2;                                      \
                                goto done;                                     \
                            }                                                  \
                        }                                                      \
                        while (idx2 < (head).size);                            \
                    }                                                          \
                    break;                                                     \
                }                                                              \
                else if (cmp < 0) {                                            \
                    eidx = idx;                                                \
                }                                                              \
                else {                                                         \
                    sidx = idx + 1;                                            \
                }                                                              \
            }                                                                  \
        }                                                                      \
    done:                                                                      \
        ret;                                                                   \
    })

#ifdef __cplusplus
}
#endif
