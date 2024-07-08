#pragma once

#include "config.h"
#include "task.h"

#include <assert.h>
#include <stdatomic.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif
static inline monad_async_cpu_ticks_count_t
get_ticks_count(MONAD_ASYNC_CPP_STD memory_order rel)
{
    monad_async_cpu_ticks_count_t ret;
#if defined(__i386__) || defined(_M_IX86) || defined(__x86_64__) ||            \
    defined(_M_X64)
    unsigned lo, hi, aux;
    switch (rel) {
    case MONAD_ASYNC_CPP_STD memory_order_acquire:
        __asm__ __volatile__("rdtsc\nlfence" : "=a"(lo), "=d"(hi));
        break;
    case MONAD_ASYNC_CPP_STD memory_order_release:
        __asm__ __volatile__("mfence\nrdtscp\n"
                             : "=a"(lo), "=d"(hi), "=c"(aux));
        break;
    case MONAD_ASYNC_CPP_STD memory_order_acq_rel:
    case MONAD_ASYNC_CPP_STD memory_order_seq_cst:
        __asm__ __volatile__("mfence\nrdtscp\nlfence"
                             : "=a"(lo), "=d"(hi), "=c"(aux));
        break;
    default:
        __asm__ __volatile__("rdtsc" : "=a"(lo), "=d"(hi));
        break;
    }
    ret = (uint64_t)lo | ((uint64_t)hi << 32);
#elif defined(__aarch64__) || defined(_M_ARM64)
    uint64_t value = 0;
    switch (rel) {
    case MONAD_ASYNC_CPP_STD memory_order_acquire:
        __asm__ __volatile__("mrs %0, PMCCNTR_EL0; dsb"
                             : "=r"(value)); // NOLINT
        break;
    case MONAD_ASYNC_CPP_STD memory_order_release:
        __asm__ __volatile__("dsb; mrs %0, PMCCNTR_EL0"
                             : "=r"(value)); // NOLINT
        break;
    case MONAD_ASYNC_CPP_STD memory_order_acq_rel:
    case MONAD_ASYNC_CPP_STD memory_order_seq_cst:
        __asm__ __volatile__("dsb; mrs %0, PMCCNTR_EL0; dsb"
                             : "=r"(value)); // NOLINT
        break;
    default:
        __asm__ __volatile__("mrs %0, PMCCNTR_EL0" : "=r"(value)); // NOLINT
        break;
    }
    ret = value;
#else
    #error "Unsupported platform"
#endif
    return ret;
}

struct io_buffer_awaiting_list_item_t
{
    struct io_buffer_awaiting_list_item_t *prev, *next;
};
struct monad_async_executor_impl;

struct monad_async_task_impl
{
    struct monad_async_task_head head;
    char magic[8];
    struct monad_async_task_impl *prev, *next;
    monad_async_context context;
    bool please_cancel_invoked;
    monad_async_result (*please_cancel)(
        struct monad_async_executor_impl *ex,
        struct monad_async_task_impl *task);

    struct
    {
        monad_async_io_status *front, *back;
        size_t count;
    } io_submitted, io_completed;

    struct io_buffer_awaiting_list_item_t io_buffer_awaiting;
    bool io_buffer_awaiting_was_inserted_at_front;
    bool io_buffer_awaiting_is_for_write;
    bool io_buffer_awaiting_is_for_large_page;

    monad_async_io_status **completed;

    /* Set this to have it executed next time executor run regains control at:

    - After task has exited and been fully detached from its executor.
    */
    monad_async_result (*call_after_suspend_to_executor)(
        struct monad_async_task_impl *task);
    void *call_after_suspend_to_executor_data;
};

static inline monad_async_priority monad_async_task_effective_cpu_priority(
    const struct monad_async_task_impl *task)
{
    return task->io_buffer_awaiting_was_inserted_at_front
               ? monad_async_priority_high
               : task->head.priority.cpu;
}

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
