#pragma once

#include <evmc/evmc.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_execution_event_type : uint8_t
{
    MONAD_PROPOSE_BLOCK = 0,
    MONAD_FINALIZE_BLOCK = 1,
    MONAD_VERIFY_BLOCK = 2,
};

static_assert(sizeof(enum monad_execution_event_type) == 1);
static_assert(alignof(enum monad_execution_event_type) == 1);

struct monad_execution_event
{
    enum monad_execution_event_type kind;
    struct evmc_bytes32 id;
};

static_assert(sizeof(struct monad_execution_event) == 33);
static_assert(alignof(struct monad_execution_event) == 1);

#ifdef __cplusplus
}
#endif
