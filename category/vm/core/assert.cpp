#include <cstdlib>
#include <print>

extern char const *__progname; // NOLINT(bugprone-reserved-identifier)

extern "C" void __attribute__((noreturn)) monad_vm_assertion_failed(
    char const *expr, char const *function, char const *file, long line)
{
    std::print(
        stderr,
        "{}: {}:{}: {}: Assertion '{}' failed.\n",
        __progname,
        file,
        line,
        function,
        expr);

    std::abort();
}
