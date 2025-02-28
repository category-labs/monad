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

    [MONAD_EVENT_BLOCK_START] =
        {.type = MONAD_EVENT_BLOCK_START,
         .c_name = "BLOCK_START",
         .description = "Started execution of a proposed block"},

    [MONAD_EVENT_BLOCK_END] =
        {.type = MONAD_EVENT_BLOCK_END,
         .c_name = "BLOCK_END",
         .description = "Proposed block with this flow ID has completed "
                        "execution (may not be finalized)"},

    [MONAD_EVENT_BLOCK_FINALIZE] =
        {.type = MONAD_EVENT_BLOCK_FINALIZE,
         .c_name = "BLOCK_FINALIZE",
         .description = "Block is committed on the canonical blockchain"},

    [MONAD_EVENT_BLOCK_REJECT] =
        {.type = MONAD_EVENT_BLOCK_REJECT,
         .c_name = "BLOCK_REJECT",
         .description = "Block failed validation and was rejected"},

    [MONAD_EVENT_BLOCK_EXEC_ERROR] =
        {.type = MONAD_EVENT_BLOCK_EXEC_ERROR,
         .c_name = "BLOCK_EXEC_ERROR",
         .description = "Block execution failed due to error in the EVM, not "
                        "due to it being invalid"},

    [MONAD_EVENT_TXN_START] =
        {.type = MONAD_EVENT_TXN_START,
         .c_name = "TXN_START",
         .description = "Started execution of new transaction"},

    [MONAD_EVENT_TXN_REJECT] =
        {.type = MONAD_EVENT_TXN_REJECT,
         .c_name = "TXN_REJECT",
         .description = "Transaction failed validation and was rejected - no "
                        "receipt, not in block"},

    [MONAD_EVENT_TXN_EXEC_ERROR] =
        {.type = MONAD_EVENT_TXN_EXEC_ERROR,
         .c_name = "TXN_EXEC_ERROR",
         .description = "Transaction execution failed due to error in the EVM, "
                        "not due to it being invalid"},

    [MONAD_EVENT_TXN_LOG] =
        {.type = MONAD_EVENT_TXN_LOG,
         .c_name = "TXN_LOG",
         .description =
             "Transaction emitted a log during speculative execution"},

    [MONAD_EVENT_TXN_RECEIPT] =
        {.type = MONAD_EVENT_TXN_RECEIPT,
         .c_name = "TXN_RECEIPT",
         .description =
             "Transaction execution finished (merged into proposed block"},

    [MONAD_EVENT_WR_ACCT_STATE_BALANCE] =
        {.type = MONAD_EVENT_WR_ACCT_STATE_BALANCE,
         .c_name = "WR_ACCT_STATE_BALANCE",
         .description = "Account balance updated by transaction commit"},

    [MONAD_EVENT_WR_ACCT_STATE_STORAGE] =
        {.type = MONAD_EVENT_WR_ACCT_STATE_STORAGE,
         .c_name = "WR_ACCT_STATE_STORAGE",
         .description = "Account storage updated by transaction commit"},
};

size_t const g_monad_event_metadata_size = 14;

uint8_t const g_monad_event_metadata_hash[32] = {
    0x19, 0xfb, 0xea, 0x06, 0xb6, 0xac, 0x94, 0x1f, 0xe0, 0xfe, 0xc4,
    0x9e, 0x98, 0xb7, 0x57, 0xff, 0x3f, 0x8d, 0xa0, 0x74, 0xff, 0x0c,
    0x1c, 0xf3, 0xbe, 0x70, 0x31, 0xfe, 0x6a, 0xbc, 0x7b, 0x7f,
};

#ifdef __cplusplus
} // extern "C"
#endif
