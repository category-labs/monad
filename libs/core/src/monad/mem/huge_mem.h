#pragma once

#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct huge_mem
{
    size_t size;
    unsigned char *data;
};

typedef struct huge_mem huge_mem_t;

static_assert(sizeof(huge_mem_t) == 16);
static_assert(alignof(huge_mem_t) == 8);

void huge_mem_alloc(huge_mem_t *, size_t);
void huge_mem_free(huge_mem_t *);

#ifdef __cplusplus
}
#endif
