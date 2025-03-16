#include <assert.h>
#include <err.h>
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sysexits.h>

#include <monad/core/c_result.h>
#include <monad/fiber/fiber.h>

// This is the function that will run on the fiber
monad_c_result say_hello_fiber_function(monad_fiber_args_t mfa)
{
    // The fiber greets you by your name, which is passed in as the fiber's
    // first function argument
    char const *const name = (char const *)mfa.arg[0];

    // Say hello, then suspend the fiber
    printf("Hello, %s!\n", name);
    monad_fiber_yield(monad_c_make_success(0));

    // When we reach here, we've been run again; we resume from the
    // suspension point of the yield immediately above. We'll say hello
    // again, then suspend again
    printf("Welcome back, %s!\n", name);
    monad_fiber_yield(monad_c_make_success(0));

    // Resumed for the final time; say goodbye, then return. Returning from
    // the fiber function suspends the fiber until it is given a new function
    // to run
    printf("Farewell, %s!\n", name);
    return monad_c_make_success(0);
}

int main(int argc, char **argv)
{
    int rc;
    monad_fiber_t *hello_fiber;
    char const *name;
    monad_allocator_t *const alloc = nullptr; // Use default allocator
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = 1UL << 17, // 128 KiB stack
        .alloc = alloc};

    // This application says hello to you using a fiber; it expects your name
    // as the first (and only) positional argument
    if (argc != 2) {
        errx(EX_USAGE, "usage: %s <your-name>", argv[0]);
    }
    name = argv[1];

    // Create the fiber, passing in our creation attributes
    rc = monad_fiber_create(&fiber_attr, &hello_fiber);
    if (rc != 0) {
        errno = rc;
        err(1, "monad_fiber_create failed");
    }

    // Tell the fiber what function to run; the second argument is
    // the scheduling priority, which doesn't matter in this example;
    // the last parameter is passed into the fiber function, as the
    // argument. We pass a pointer to our name
    rc = monad_fiber_set_function(
        hello_fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        say_hello_fiber_function,
        (monad_fiber_args_t){.arg = {(uintptr_t)name}});
    assert(rc == 0);

    // Run the fiber until the first suspension point; this will print
    // "Hello, <name>!", suspend the fiber function, and then our call to
    // monad_fiber_run will return. If nothing goes wrong, the return code
    // will be 0. The second parameter (which is nullptr here) allows us to
    // obtain information about why the fiber suspended; in this example we
    // don't care, so we pass nullptr
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == 0);

    // Run the fiber again, until it yields again; this will print
    // "Welcome back, <name>!" and then yield back to us once more
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == 0);

    // Run the fiber a final time. This will print "Farewell, <name>!" and then
    // the fiber function will return. The return won't look much different to
    // us than the yields above: the fiber will suspend and monad_fiber_run will
    // return 0 to us, as before. The difference is, we can't run the fiber
    // again. If, instead of passing nullptr as the second argument, we instead
    // passed a pointer to a `monad_fiber_suspend_info_t`, we could get more
    // information about the suspension. Namely, that it was a return and not a
    // yield, and we could also read the `monad_c_result` return code. However,
    // we don't care in this example.
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == 0);

    // Try to run the fiber one more time; we can't do it since the fiber
    // function returned, so this will fail and return the errno-domain error
    // code ENXIO
    rc = monad_fiber_run(hello_fiber, nullptr);
    assert(rc == ENXIO);

    // At this point, we could reuse the fiber's resources to run the function
    // a second time. To prepare for a second run, we would reset the function:
    rc = monad_fiber_set_function(
        hello_fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        say_hello_fiber_function,
        (monad_fiber_args_t){.arg = {(uintptr_t)name}});
    assert(rc == 0);

    // However, that's enough for today; destroy the fiber and exit.
    monad_fiber_destroy(hello_fiber);
    return 0;
}
