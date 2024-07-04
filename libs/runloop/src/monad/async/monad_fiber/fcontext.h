#pragma once

#include <stddef.h>

#if defined(BOOST_CONTEXT_DETAIL_FCONTEXT_H)

using boost::context::detail::fcontext_t;
using boost::context::detail::jump_fcontext;
using boost::context::detail::make_fcontext;
using boost::context::detail::ontop_fcontext;

#else
    #if defined(__cplusplus)
        #include <cstddef>
extern "C"
{
    #else
        #include <stddef.h>
    #endif

typedef void *fcontext_t;

struct transfer_t
{
    fcontext_t fctx;
    void *data;
};

struct transfer_t jump_fcontext(fcontext_t const to, void *vp);
fcontext_t make_fcontext(void *sp, size_t size, void (*fn)(struct transfer_t));
struct transfer_t ontop_fcontext(
    fcontext_t const to, void *vp, struct transfer_t (*fn)(struct transfer_t));

    #if defined(__cplusplus)
}
    #endif

#endif
