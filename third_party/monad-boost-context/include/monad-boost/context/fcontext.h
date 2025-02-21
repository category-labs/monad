#pragma once

#include <stddef.h>

#if defined(__cplusplus)
extern "C"
{
#endif

typedef void *monad_fcontext_t;

struct monad_transfer_t
{
    monad_fcontext_t fctx;
    void *data;
};

struct monad_transfer_t
monad_jump_fcontext(monad_fcontext_t const to, void *vp);
monad_fcontext_t
monad_make_fcontext(void *sp, size_t size, void (*fn)(struct monad_transfer_t));
struct monad_transfer_t monad_ontop_fcontext(
    monad_fcontext_t const to, void *vp,
    struct monad_transfer_t (*fn)(struct monad_transfer_t));

#if defined(__cplusplus)
}
#endif
