#include <stddef.h>
#include <stdint.h>

#include <category/core/event/event_metadata.h>
#include <category/core/event/test_event_ctypes.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_metadata const g_monad_test_event_metadata[2] = {

    [MONAD_TEST_EVENT_NONE] =
        {.event_type = MONAD_TEST_EVENT_NONE,
         .c_name = "NONE",
         .description = "reserved code so that 0 remains invalid"},

    [MONAD_TEST_EVENT_COUNTER] =
        {.event_type = MONAD_TEST_EVENT_COUNTER,
         .c_name = "TEST_COUNTER",
         .description = "A special event emitted only by the test suite"},

};

uint8_t const g_monad_test_event_schema_hash[32] = {};

#ifdef __cplusplus
} // extern "C"
#endif
