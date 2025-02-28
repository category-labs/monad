#include <stddef.h>
#include <stdint.h>

#include <monad/event/event_metadata.h>
#include <monad/event/event_types.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_metadata const g_monad_event_metadata[] = {

    [MONAD_EVENT_NONE] =
        {.type = MONAD_EVENT_NONE,
         .c_name = "NONE",
         .description = "reserved code so that 0 remains invalid"},

    [MONAD_EVENT_TEST_COUNTER] =
        {.type = MONAD_EVENT_TEST_COUNTER,
         .c_name = "TEST_COUNTER",
         .description = "A special event emitted only by the test suite"},

};

size_t const g_monad_event_metadata_size = 2;

uint8_t const g_monad_event_metadata_hash[32] = {
    0x85, 0xda, 0x78, 0xa2, 0x79, 0xfb, 0xed, 0x17, 0xe2, 0x46, 0xbc,
    0x20, 0x76, 0xd6, 0xcd, 0x4a, 0x62, 0xb2, 0x1d, 0x4b, 0x3c, 0x7d,
    0xdd, 0xd1, 0x7f, 0xcd, 0x0d, 0xab, 0x96, 0x20, 0xdf, 0x37,
};

#ifdef __cplusplus
} // extern "C"
#endif
