#include <category/core/thread/thread_pool.hpp>

MONAD_NAMESPACE_BEGIN

static cpu_set_t cpu_set{};
static ThreadPool pool{4, cpu_set};

MONAD_NAMESPACE_END
