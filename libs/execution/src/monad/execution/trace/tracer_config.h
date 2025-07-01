#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

enum tracer_config
{
    NOOP_TRACER = 0,
    CALL_TRACER = 1,
    PRESTATE_TRACER = 2,
    STATEDIFF_TRACER = 3,
};

#ifdef __cplusplus
}
#endif
