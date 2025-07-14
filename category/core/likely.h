#pragma once

#define MONAD_LIKELY(x) __builtin_expect(!!(x), 1)
#define MONAD_UNLIKELY(x) __builtin_expect(!!(x), 0)
