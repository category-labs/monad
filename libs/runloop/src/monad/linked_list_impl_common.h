#pragma once

#include "context/config.h"

#include <assert.h>
#include <stdatomic.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define LIST_DEFINE_REMOVE_STRUCT_struct
#define LIST_DEFINE_TYPE_NAME3(prefix, x) prefix##_##x##_t
#define LIST_DEFINE_TYPE_NAME2(prefix, x) LIST_DEFINE_TYPE_NAME3(prefix, x)
#define LIST_DEFINE_TYPE_NAME(prefix, x)                                       \
    LIST_DEFINE_TYPE_NAME2(prefix, LIST_DEFINE_REMOVE_STRUCT_##x)

#define LIST_DECLARE_N(type)                                                   \
    struct LIST_DEFINE_TYPE_NAME(list_define_n, type)                          \
    {                                                                          \
        type *front, *back;                                                    \
        size_t count;                                                          \
    }
#define LIST_DECLARE_P(type)                                                   \
    struct LIST_DEFINE_TYPE_NAME(list_define_p, type)                          \
    {                                                                          \
        type *front, *back;                                                    \
        size_t count;                                                          \
    }

#define LIST_DEFINE_N(name, type)                                              \
    struct LIST_DEFINE_TYPE_NAME(list_define_n, type) name
#define LIST_DEFINE_P(name, type)                                              \
    struct LIST_DEFINE_TYPE_NAME(list_define_p, type)                          \
        name[monad_async_priority_max]
#ifdef NDEBUG
    #define LIST_CHECK(list, item)
#else
    #define LIST_CHECK(list, item)                                             \
        {                                                                      \
            typeof((list).front) _item_ = (list).front;                        \
            bool found = false;                                                \
            for (size_t _n_ = 0; _n_ < (list).count; _n_++) {                  \
                assert(                                                        \
                    (_n_ + 1 == (list).count && _item_->next == nullptr) ||    \
                    _item_->next != nullptr);                                  \
                assert(                                                        \
                    (_n_ == 0 && _item_->prev == nullptr) ||                   \
                    _item_->prev != nullptr);                                  \
                if ((item) == _item_) {                                        \
                    found = true;                                              \
                }                                                              \
                _item_ = _item_->next;                                         \
            }                                                                  \
            assert((item) == nullptr || found);                                \
            _item_ = (list).back;                                              \
            found = false;                                                     \
            for (size_t _n_ = 0; _n_ < (list).count; _n_++) {                  \
                assert(                                                        \
                    (_n_ + 1 == (list).count && _item_->prev == nullptr) ||    \
                    _item_->prev != nullptr);                                  \
                assert(                                                        \
                    (_n_ == 0 && _item_->next == nullptr) ||                   \
                    _item_->next != nullptr);                                  \
                if ((item) == _item_) {                                        \
                    found = true;                                              \
                }                                                              \
                _item_ = _item_->prev;                                         \
            }                                                                  \
            assert((item) == nullptr || found);                                \
        }
#endif
#define LIST_PREPEND2(list, item, counter, inc, dec)                           \
    assert((item)->prev == nullptr);                                           \
    assert((item)->next == nullptr);                                           \
    if ((list).front == nullptr) {                                             \
        assert((list).back == nullptr);                                        \
        assert((list).count == 0);                                             \
        (item)->prev = (item)->next = nullptr;                                 \
        (list).front = (list).back = (item);                                   \
        (list).count++;                                                        \
        if ((counter) != nullptr)                                              \
            inc(*counter);                                                     \
    }                                                                          \
    else {                                                                     \
        assert((list).front->prev == nullptr);                                 \
        assert((list).count == 1 || (list).front->next != nullptr);            \
        (item)->prev = nullptr;                                                \
        (item)->next = (list).front;                                           \
        (list).front->prev = (item);                                           \
        (list).front = (item);                                                 \
        (list).count++;                                                        \
        if ((counter) != nullptr)                                              \
            inc(*counter);                                                     \
    }                                                                          \
    LIST_CHECK(list, item)
#define LIST_APPEND2(list, item, counter, inc, dec)                            \
    assert((item)->prev == nullptr);                                           \
    assert((item)->next == nullptr);                                           \
    if ((list).back == nullptr) {                                              \
        assert((list).front == nullptr);                                       \
        assert((list).count == 0);                                             \
        (item)->prev = (item)->next = nullptr;                                 \
        (list).front = (list).back = (item);                                   \
        (list).count++;                                                        \
        if ((counter) != nullptr)                                              \
            inc(*counter);                                                     \
    }                                                                          \
    else {                                                                     \
        assert((list).back->next == nullptr);                                  \
        assert((list).count == 1 || (list).back->prev != nullptr);             \
        (item)->next = nullptr;                                                \
        (item)->prev = (list).back;                                            \
        (list).back->next = (item);                                            \
        (list).back = (item);                                                  \
        (list).count++;                                                        \
        if ((counter) != nullptr)                                              \
            inc(*counter);                                                     \
    }                                                                          \
    LIST_CHECK(list, item)
// Note inserts BEFORE pos. pos cannot be first item (use prepend!)
#define LIST_INSERT2(list, pos, item, counter, inc, dec)                       \
    assert((item)->prev == nullptr);                                           \
    assert((item)->next == nullptr);                                           \
    assert((pos)->prev != nullptr);                                            \
    (item)->next = (pos);                                                      \
    (item)->prev = (pos)->prev;                                                \
    (pos)->prev = (item);                                                      \
    (item)->prev->next = (item);                                               \
    (list).count++;                                                            \
    if ((counter) != nullptr)                                                  \
        inc(*counter);                                                         \
    LIST_CHECK(list, item)
#define LIST_REMOVE2(list, item, counter, inc, dec)                            \
    LIST_CHECK(list, item)                                                     \
    if ((list).front == (item) && (list).back == (item)) {                     \
        assert((list).count == 1);                                             \
        (list).front = (list).back = nullptr;                                  \
        (list).count = 0;                                                      \
        (item)->next = (item)->prev = nullptr;                                 \
        if ((counter) != nullptr)                                              \
            dec(*counter);                                                     \
    }                                                                          \
    else if ((list).front == (item)) {                                         \
        assert((item)->prev == nullptr);                                       \
        (item)->next->prev = nullptr;                                          \
        (list).front = (item)->next;                                           \
        (list).count--;                                                        \
        (item)->next = (item)->prev = nullptr;                                 \
        if ((counter) != nullptr)                                              \
            dec(*counter);                                                     \
    }                                                                          \
    else if ((list).back == (item)) {                                          \
        assert((item)->next == nullptr);                                       \
        (item)->prev->next = nullptr;                                          \
        (list).back = (item)->prev;                                            \
        (list).count--;                                                        \
        (item)->next = (item)->prev = nullptr;                                 \
        if ((counter) != nullptr)                                              \
            dec(*counter);                                                     \
    }                                                                          \
    else {                                                                     \
        (item)->prev->next = (item)->next;                                     \
        (item)->next->prev = (item)->prev;                                     \
        (list).count--;                                                        \
        (item)->next = (item)->prev = nullptr;                                 \
        if ((counter) != nullptr)                                              \
            dec(*counter);                                                     \
    }                                                                          \
    LIST_CHECK(list, nullptr)

#define LIST_COUNTER_INCR(item) (item)++
#define LIST_COUNTER_DECR(item) (item)--
#define LIST_PREPEND(list, item, counter)                                      \
    LIST_PREPEND2(list, item, counter, LIST_COUNTER_INCR, LIST_COUNTER_DECR)
#define LIST_APPEND(list, item, counter)                                       \
    LIST_APPEND2(list, item, counter, LIST_COUNTER_INCR, LIST_COUNTER_DECR)
#define LIST_INSERT(list, pos, item, counter)                                  \
    LIST_INSERT2(list, pos, item, counter, LIST_COUNTER_INCR, LIST_COUNTER_DECR)
#define LIST_REMOVE(list, item, counter)                                       \
    LIST_REMOVE2(list, item, counter, LIST_COUNTER_INCR, LIST_COUNTER_DECR)

#define LIST_ATOMIC_COUNTER_INCR(item)                                         \
    atomic_fetch_add_explicit((&item), 1, memory_order_relaxed)
#define LIST_ATOMIC_COUNTER_DECR(item)                                         \
    atomic_fetch_sub_explicit((&item), 1, memory_order_relaxed)
#define LIST_PREPEND_ATOMIC_COUNTER(list, item, counter)                       \
    LIST_PREPEND2(                                                             \
        list,                                                                  \
        item,                                                                  \
        counter,                                                               \
        LIST_ATOMIC_COUNTER_INCR,                                              \
        LIST_ATOMIC_COUNTER_DECR)
#define LIST_APPEND_ATOMIC_COUNTER(list, item, counter)                        \
    LIST_APPEND2(                                                              \
        list,                                                                  \
        item,                                                                  \
        counter,                                                               \
        LIST_ATOMIC_COUNTER_INCR,                                              \
        LIST_ATOMIC_COUNTER_DECR)
#define LIST_INSERT_ATOMIC_COUNTER(list, pos, item, counter)                   \
    LIST_INSERT2(                                                              \
        list,                                                                  \
        pos,                                                                   \
        item,                                                                  \
        counter,                                                               \
        LIST_ATOMIC_COUNTER_INCR,                                              \
        LIST_ATOMIC_COUNTER_DECR)
#define LIST_REMOVE_ATOMIC_COUNTER(list, item, counter)                        \
    LIST_REMOVE2(                                                              \
        list,                                                                  \
        item,                                                                  \
        counter,                                                               \
        LIST_ATOMIC_COUNTER_INCR,                                              \
        LIST_ATOMIC_COUNTER_DECR)

#ifdef __cplusplus
}
#endif
