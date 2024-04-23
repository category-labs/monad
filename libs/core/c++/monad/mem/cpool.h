#pragma once

#include <monad/core/likely.h>

#include <assert.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>

/**
 * memory pool where old allocations expire as new allocations are made
 * implemented via a circular queue
 */

#define CPOOL_DEFINE(BITS)                                                     \
                                                                               \
    typedef struct                                                             \
    {                                                                          \
        uint32_t next;                                                         \
    } cpool_##BITS##_t;                                                        \
                                                                               \
    static_assert(sizeof(cpool_##BITS##_t) == 4, "");                          \
    static_assert(alignof(cpool_##BITS##_t) == 4, "");                         \
                                                                               \
    static inline cpool_##BITS##_t *cpool_init##BITS(unsigned char *const mem) \
    {                                                                          \
        cpool_##BITS##_t *const p = (cpool_##BITS##_t *)mem;                   \
        p->next = sizeof(cpool_##BITS##_t);                                    \
        return p;                                                              \
    }                                                                          \
                                                                               \
    static inline unsigned char *cpool_ptr##BITS(                              \
        cpool_##BITS##_t const *const p, uint32_t const i)                     \
    {                                                                          \
        return (unsigned char *)p + (i & ((1u << BITS) - 1));                  \
    }                                                                          \
                                                                               \
    static inline uint32_t cpool_reserve##BITS(                                \
        cpool_##BITS##_t *const p, uint32_t const n)                           \
    {                                                                          \
        uint32_t m_next = p->next & ((1u << BITS) - 1);                        \
        if (MONAD_UNLIKELY(m_next + n > (1u << BITS))) {                       \
            p->next += (1u << BITS) - m_next;                                  \
            m_next = p->next & ((1u << BITS) - 1);                             \
        }                                                                      \
        if (MONAD_UNLIKELY(m_next < sizeof(cpool_##BITS##_t))) {               \
            p->next += (uint32_t)sizeof(cpool_##BITS##_t) - m_next;            \
        }                                                                      \
        return p->next;                                                        \
    }                                                                          \
                                                                               \
    static inline void cpool_advance##BITS(                                    \
        cpool_##BITS##_t *const p, uint32_t const n)                           \
    {                                                                          \
        p->next += n;                                                          \
    }                                                                          \
                                                                               \
    /**                                                                        \
     * valid objects are in [next - SIZE, next)                                \
     * invalid objects are in [next, next - SIZE)                              \
     */                                                                        \
    static inline bool cpool_valid##BITS(                                      \
        cpool_##BITS##_t const *const p, uint32_t const i)                     \
    {                                                                          \
        bool valid = false;                                                    \
        if (MONAD_UNLIKELY((1u << BITS) > p->next)) {                          \
            if (i < p->next || i >= p->next - (1u << BITS)) {                  \
                valid = true;                                                  \
            }                                                                  \
        }                                                                      \
        else if (MONAD_LIKELY(i >= p->next - (1u << BITS) && i < p->next)) {   \
            valid = true;                                                      \
        }                                                                      \
        return valid;                                                          \
    }
