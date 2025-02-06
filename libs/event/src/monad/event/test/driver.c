/**
 * @file
 *
 * A simple command line driver that exposes a "fake event server". Typically,
 * the fake event server library is embedded directly in a test binary to avoid
 * needing to connect to a separate process, but sometimes a freestanding
 * fake server is useful for debugging.
 */

#include <stdio.h>

#include <err.h>
#include <errno.h>
#include <signal.h>
#include <sysexits.h>
#include <time.h>
#include <unistd.h>

#include <monad/event/event_server.h>

extern int monad_event_test_server_create_from_file(
    char const *socket_path, FILE *log_file, char const *capture_path,
    struct monad_event_server **server_p);

extern char const *__progname;

static void usage(FILE *out)
{
    fprintf(out, "usage: %s <socket-file> <shm-capture-file>\n", __progname);
}

static sig_atomic_t g_exit = 0;

static void set_exit(int)
{
    g_exit = 1;
}

int main(int argc, char **argv)
{
    int rc;
    struct monad_event_server *server;
    struct timespec const one_second = {.tv_sec = 1, .tv_nsec = 0};

    if (argc != 3) {
        usage(stderr);
        return EX_USAGE;
    }
    rc = monad_event_test_server_create_from_file(
        argv[1], stderr, argv[2], &server);
    if (rc != 0) {
        errno = rc;
        err(EX_SOFTWARE, "unable to create test server");
    }
    signal(SIGINT, set_exit);
    while (g_exit == 0) {
        rc = monad_event_server_process_work(
            server, &one_second, nullptr, nullptr);
        if (rc != 0) {
            errno = rc;
            err(EX_SOFTWARE, "event server returned an error");
        }
    }
    monad_event_server_destroy(server);
    unlink(argv[1]);
    return 0;
}
