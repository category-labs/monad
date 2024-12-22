/**
 * @file
 *
 * This file implements most of the event server functionality, except for
 * the functions that export the shared memory segments. Delegating that task
 * permits this file to only be concerned with the ceremony of "being a
 * server": managing client objects, running the event loop, doing I/O, etc.
 *
 * Namely, it does not understand the memory layout of the event rings and does
 * not include any of the event recorder headers. This allows the code to be
 * reused to create the fake event server for testing purposes, without the
 * user of the fake server needing to link the full libmonad_core.a. This is
 * important because the latter links to Rust.
 */

#include <errno.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <poll.h>
#include <sys/epoll.h>
#include <sys/queue.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <syslog.h>
#include <time.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/srcloc.h>
#include <monad/event/event.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_server.h>
#include <monad/event/event_shared.h>

#include "event_server_internal.h"

#ifdef NDEBUG
static uint64_t const NO_OPEN_TIMEOUT_NANOS = 5'000'000'000;
#else
static uint64_t const NO_OPEN_TIMEOUT_NANOS = 60'000'000'000;
#endif

// Client of the event server, connected over a socket
struct monad_event_client
{
    int sock_fd;
    unsigned client_id;
    unsigned exported_rings;
    struct monad_event_server *server;
    struct sockaddr_un sock_addr;
    TAILQ_ENTRY(monad_event_client) next;
    uint64_t connect_epoch_nanos;
};

// Resources for the event server
struct monad_event_server
{
    int sock_fd;
    int epoll_fd;
    TAILQ_HEAD(, monad_event_client) clients;
    unsigned last_client_id;
    uint64_t last_heartbeat_time;
    struct shared_mem_export_ops const *export_ops;
    void *export_state;
    uint64_t export_count;
    struct monad_event_server_options create_options;
    struct sockaddr_un server_addr;
};

__attribute__((format(printf, 6, 7))) static int write_log(
    monad_event_server_log_fn *log_fn, void *log_context, int severity, int err,
    monad_source_location_t const *srcloc, char const *format, ...)
{
    va_list ap;
    static thread_local char errbuf[1024];

    if (log_fn == nullptr) {
        return err;
    }
    va_start(ap, format);
    _monad_event_vformat_err(errbuf, sizeof errbuf, srcloc, err, format, ap);
    va_end(ap);
    log_fn(severity, errbuf, log_context);
    return err;
}

#define WR_ERR(LOG_FN, LOG_CONTEXT, ERRC, FORMAT, ...)                         \
    write_log(                                                                 \
        (LOG_FN),                                                              \
        (LOG_CONTEXT),                                                         \
        LOG_ERR,                                                               \
        (ERRC),                                                                \
        &(monad_source_location_t){__FUNCTION__, __FILE__, __LINE__, 0},       \
        FORMAT __VA_OPT__(, ) __VA_ARGS__)

#define WR_INFO(LOG_FN, LOG_CONTEXT, ...)                                      \
    write_log(                                                                 \
        (LOG_FN),                                                              \
        (LOG_CONTEXT),                                                         \
        LOG_INFO,                                                              \
        0,                                                                     \
        &(monad_source_location_t){__FUNCTION__, __FILE__, __LINE__, 0},       \
        __VA_ARGS__)

#define WR_ERR_SRV(SRV, ...)                                                   \
    WR_ERR(                                                                    \
        (SRV) != nullptr ? (SRV)->create_options.log_fn : nullptr,             \
        (SRV) != nullptr ? (SRV)->create_options.log_context : nullptr,        \
        __VA_ARGS__);

#define WR_INFO_SRV(SRV, ...)                                                  \
    WR_INFO(                                                                   \
        (SRV) != nullptr ? (SRV)->create_options.log_fn : nullptr,             \
        (SRV) != nullptr ? (SRV)->create_options.log_context : nullptr,        \
        __VA_ARGS__);

// We redeclare this simple function rather than using
// `monad_event_get_epoch_nanos` because we don't want to include
// event_recorder.h directly here.
static uint64_t get_epoch_nanos()
{
    struct timespec now;
    (void)clock_gettime(CLOCK_REALTIME, &now);
    return (uint64_t)(now.tv_sec * 1'000'000'000L + now.tv_nsec);
}

/*
 * Client management functions
 */

static void close_client(struct monad_event_client *client)
{
    TAILQ_REMOVE(&client->server->clients, client, next);
    (void)close(client->sock_fd);
    WR_INFO_SRV(client->server, "event client %u closed", client->client_id);
    free(client);
}

static void close_client_err(
    struct monad_event_client *client, int error, char const *format, ...)
{
    va_list ap;
    struct monad_event_export_error_msg msg;
    size_t send_size;
    int len;

    msg.msg_type = MONAD_EVENT_MSG_EXPORT_ERROR;
    msg.error_code = error;
    va_start(ap, format);
    len = vsnprintf(msg.error_buf, sizeof msg.error_buf, format, ap);
    va_end(ap);
    if (len > 0) {
        send_size = offsetof(struct monad_event_export_error_msg, error_buf) +
                    (size_t)len + 1;
        if (send(client->sock_fd, &msg, send_size, 0) == -1) {
            WR_ERR_SRV(
                client->server,
                errno,
                "unable to send error message about dying client: %u",
                client->client_id);
        }
        WR_ERR_SRV(
            client->server,
            errno,
            "closing event client %u: %s",
            client->client_id,
            msg.error_buf);
    }
    close_client(client);
}

static void handle_export_ring_msg(
    struct monad_event_client *client,
    struct monad_event_export_ring_msg const *msg)
{
    unsigned nmsgs = 0;
    struct monad_event_server *const server = client->server;
    WR_INFO_SRV(
        server,
        "received EXPORT_RING:%hhu msg for client %u",
        msg->ring_type,
        client->client_id);
    if (msg->ring_type >= MONAD_EVENT_RING_COUNT) {
        return close_client_err(
            client,
            ENOSYS,
            "client tried to export unknown event ring %hhu",
            msg->ring_type);
    }
    if (server->export_ops->export_ring(
            msg,
            client->sock_fd,
            client->client_id,
            close_client_err,
            client,
            server->export_state,
            &nmsgs)) {
        ++client->exported_rings;
        ++client->server->export_count;
        WR_INFO_SRV(
            server,
            "exported %u memory segments for client "
            "%u:%hhu in %u messages",
            nmsgs - 1,
            client->client_id,
            msg->ring_type,
            nmsgs);
    }
}

static void accept_client(struct monad_event_server *server)
{
    struct sockaddr_un client_addr;
    socklen_t client_addr_size = sizeof client_addr;
    struct monad_event_client *client;
    struct epoll_event evt;
    int client_fd;
    unsigned nmsgs = 0;

    client_fd = accept4(
        server->sock_fd,
        (struct sockaddr *)&client_addr,
        &client_addr_size,
        SOCK_CLOEXEC);
    if (client_fd == -1) {
        WR_ERR_SRV(server, errno, "accept4(2) failed for next client");
        return;
    }
    client = malloc(sizeof *client);
    if (client == nullptr) {
        WR_ERR_SRV(server, errno, "malloc(3) failed for client");
        (void)close(client_fd);
    }
    memset(client, 0, sizeof *client);
    TAILQ_INSERT_TAIL(&server->clients, client, next);
    client->sock_fd = client_fd;
    client->client_id = ++server->last_client_id;
    client->server = server;
    memcpy(&client->sock_addr, &client_addr, client_addr_size);
    WR_INFO_SRV(
        server, "new connection from event client %u", client->client_id);
    client->connect_epoch_nanos = get_epoch_nanos();

    evt.events = EPOLLIN;
    evt.data.ptr = client;
    if (epoll_ctl(server->epoll_fd, EPOLL_CTL_ADD, client_fd, &evt) == -1) {
        WR_ERR_SRV(server, errno, "epoll_ctl(2) adding client socket failed");
        close_client(client);
    }

    if (server->export_ops->export_metadata(
            client->sock_fd,
            client->client_id,
            close_client_err,
            client,
            server->export_state,
            &nmsgs)) {
        WR_INFO_SRV(
            server,
            "exported metadata information to "
            "client %u in %u messages",
            client->client_id,
            nmsgs);
    }
}

/*
 * Client socket I/O functions
 */

static void handle_client_socket_read(struct monad_event_client *client)
{
    struct monad_event_export_ring_msg msg;

    if (recv(client->sock_fd, &msg, sizeof msg, 0) == -1) {
        WR_ERR_SRV(
            client->server,
            errno,
            "recv(2) from event client %u failed",
            client->client_id);
        close_client(client);
    }
    switch (msg.msg_type) {
    case MONAD_EVENT_MSG_EXPORT_RING:
        return handle_export_ring_msg(client, &msg);

    default:
        close_client_err(
            client, EPROTO, "unexpected client message type %u", msg.msg_type);
    }
}

static void process_client_socket_event(
    struct monad_event_client *client, struct epoll_event const *event)
{
    int sockerr;
    socklen_t optlen;

    if (event->events & EPOLLRDHUP) {
        // Client did a shutdown(SHUT_WR); we don't care about this
        WR_INFO_SRV(
            client->server,
            "event client %u shut down writing",
            client->client_id);
        return;
    }
    if (event->events & EPOLLHUP) {
        // Client disconnected
        WR_INFO_SRV(
            client->server,
            "event client %u closed socket connection",
            client->client_id);
        return close_client(client);
    }
    if (event->events & EPOLLERR) {
        sockerr = 0;
        optlen = sizeof sockerr;
        if (getsockopt(
                client->sock_fd, SOL_SOCKET, SO_ERROR, &sockerr, &optlen) ==
            -1) {
            WR_ERR_SRV(
                client->server,
                errno,
                "getsockopt(2) of SO_ERROR on event client %u socket failed",
                client->client_id);
        }
        else {
            WR_ERR_SRV(
                client->server,
                sockerr,
                "error on event client %u socket",
                client->client_id);
        }
        // Close the client, we're not sure how to continue after this
        return close_client_err(client, sockerr, "disconnected by EPOLLERR");
    }
    MONAD_ASSERT(event->events & EPOLLIN);
    handle_client_socket_read(client);
}

/*
 * Server socket I/O functions
 */

static void process_server_socket_event(
    struct monad_event_server *server, struct epoll_event const *event)
{
    int sockerr;
    socklen_t optlen;

    if (event->events & EPOLLIN) {
        accept_client(server);
    }
    else {
        // This should only be some kind of socket error
        MONAD_ASSERT(event->events & EPOLLERR);
        optlen = sizeof sockerr;
        if (getsockopt(
                server->sock_fd, SOL_SOCKET, SO_ERROR, &sockerr, &optlen) ==
            -1) {
            WR_ERR_SRV(
                server,
                errno,
                "getsockopt(2) of SO_ERROR on server socket failed");
        }
        else {
            WR_ERR_SRV(server, sockerr, "error on server socket");
        }
    }
}

/*
 * Public interface of monad_event_server
 */

// monad_event_server is one-line wrapper around this function, which passes
// in the shmem export policy object, see event_server_export.c; this function
// is reused by the fake event server
int _monad_event_server_create_common(
    struct monad_event_server_options const *options,
    struct shared_mem_export_ops const *export_ops, void *export_state,
    struct monad_event_server **server_p)
{
    struct monad_event_server *server;
    struct sockaddr_un *addr;
    struct stat sock_stat;
    struct epoll_event evt;
    char const *socket_path;
    int rc;
    int saved_error;

    if (options == nullptr || server_p == nullptr) {
        return EFAULT;
    }
    *server_p = nullptr;
    socket_path =
        options->socket_path != nullptr && strlen(options->socket_path) > 0
            ? options->socket_path
            : MONAD_EVENT_DEFAULT_SOCKET_PATH;
    if (strlen(socket_path) >= sizeof addr->sun_path) {
        return WR_ERR(
            options->log_fn,
            options->log_context,
            ENAMETOOLONG,
            "socket path %s exceeds maximum length %lu",
            socket_path,
            sizeof addr->sun_path);
    }
    server = *server_p = malloc(sizeof *server);
    if (server == nullptr) {
        return WR_ERR(
            options->log_fn, options->log_context, errno, "malloc(3) failed");
    }
    memset(server, 0, sizeof *server);
    server->epoll_fd = -1; // In case we jump to `Cleanup` early
    server->sock_fd = -1;
    server->export_ops = export_ops;
    server->export_state = export_state;
    TAILQ_INIT(&server->clients);
    server->last_client_id = 0;
    memcpy(&server->create_options, options, sizeof *options);
    server->create_options.socket_path = strdup(socket_path);
    if (server->create_options.socket_path == nullptr) {
        saved_error = WR_ERR_SRV(server, errno, "strdup(3) failed");
        goto Cleanup;
    }
    server->sock_fd = socket(AF_LOCAL, SOCK_SEQPACKET, 0);
    if (server->sock_fd == -1) {
        saved_error = WR_ERR_SRV(server, errno, "socket(2) failed");
        goto Cleanup;
    }
    server->epoll_fd = epoll_create1(EPOLL_CLOEXEC);
    if (server->epoll_fd == -1) {
        saved_error = WR_ERR_SRV(server, errno, "epoll_create(1) failed");
        goto Cleanup;
    }
    addr = &server->server_addr;
    server->server_addr.sun_family = AF_LOCAL;
    // This can't fail, we've already checked for ENAMETOOLONG above
    (void)strlcpy(addr->sun_path, socket_path, sizeof addr->sun_path);
    // stat(2) whatever file is already there
    rc = stat(addr->sun_path, &sock_stat);
    if (rc == -1 && errno != ENOENT) {
        saved_error = WR_ERR_SRV(
            server,
            errno,
            "stat(2) of socket path `%s` "
            "failed",
            addr->sun_path);
        goto Cleanup;
    }
    if (rc == 0) {
        // There is already a file with this same name as the socket file.
        // If it is also a socket, we'll automatically unlink it, otherwise
        // it's an EEXIST error (we don't want to accidentally unlink something
        // they might've wanted).
        if (S_ISSOCK(sock_stat.st_mode)) {
            // This is "best efforts": if it fails for some odd reason (e.g.,
            // EBUSY) it's fine, we'll just get EADDRINUSE from bind(2).
            (void)unlink(addr->sun_path);
        }
        else {
            saved_error = WR_ERR_SRV(
                server,
                EEXIST,
                "file `%s` exists and is "
                "not a socket",
                addr->sun_path);
            goto Cleanup;
        }
    }
    // Bind to the socket address, convert it to a listening socket, and
    // add an epoll event that listens for available connections
    if (bind(server->sock_fd, (struct sockaddr const *)addr, sizeof *addr) ==
        -1) {
        saved_error = WR_ERR_SRV(
            server,
            errno,
            "bind(2) to socket address "
            "`%s` failed",
            addr->sun_path);
        goto Cleanup;
    }
    if (listen(server->sock_fd, 8)) {
        saved_error = WR_ERR_SRV(server, errno, "listen(2) failed");
        goto Cleanup;
    }
    evt.events = EPOLLIN;
    evt.data.ptr = server;
    if (epoll_ctl(server->epoll_fd, EPOLL_CTL_ADD, server->sock_fd, &evt) ==
        -1) {
        saved_error =
            WR_ERR_SRV(server, errno, "epoll_ctl(2) add of server fd failed");
        goto Cleanup;
    }
    WR_INFO_SRV(
        server, "event server socket listening on `%s`", addr->sun_path);
    return 0;

Cleanup:
    monad_event_server_destroy(server);
    *server_p = nullptr;
    return saved_error;
}

void monad_event_server_destroy(struct monad_event_server *server)
{
    struct monad_event_client *client, *to_close;
    MONAD_ASSERT(server != nullptr && server->export_ops != nullptr);
    if (server->export_ops->cleanup) {
        server->export_ops->cleanup(server->export_state);
    }
    client = TAILQ_FIRST(&server->clients);
    while (client != nullptr) {
        to_close = client;
        client = TAILQ_NEXT(client, next);
        close_client(to_close);
    }
    free((void *)server->create_options.socket_path);
    (void)close(server->sock_fd);
    (void)close(server->epoll_fd);
    free(server);
}

bool monad_event_server_has_pending_work(struct monad_event_server *server)
{
    struct pollfd pfd;
    if (server == nullptr) {
        return false;
    }
    pfd.fd = server->epoll_fd;
    pfd.events = POLLIN;
    return poll(&pfd, 1, 0) > 0;
}

int monad_event_server_process_work(
    struct monad_event_server *server, struct timespec const *timeout,
    sigset_t const *sigmask, unsigned *rings_exported)
{
#define SERVER_EPOLL_EVENT_MAX 16
    uint64_t epoch_nanos_now;
    uint64_t no_open_elapsed_nanos;
    struct epoll_event events[SERVER_EPOLL_EVENT_MAX];
    struct monad_event_client *client;
    struct monad_event_client *zombie_client;
    int nready;

    if (server == nullptr) {
        return EFAULT;
    }
    uint64_t const exports_before = server->export_count;
    if (rings_exported != nullptr) {
        *rings_exported = 0;
    }
    nready = epoll_pwait2(
        server->epoll_fd, events, SERVER_EPOLL_EVENT_MAX, timeout, sigmask);
    if (nready < 0) {
        if (errno == EINTR) {
            return 0; // Ignore EINTR
        }
        return WR_ERR_SRV(server, errno, "epoll_pwait2(2) on server failed");
    }
    for (int e = 0; e < nready; ++e) {
        if (events[e].data.ptr == server) {
            process_server_socket_event(server, &events[e]);
        }
        else {
            // Any registered event that is not for the server should be
            // associated with a `monad_event_client` object
            process_client_socket_event(events[e].data.ptr, &events[e]);
        }
    }

    // Send a heartbeat event approximately every second
    epoch_nanos_now = get_epoch_nanos();
    if (epoch_nanos_now - server->last_heartbeat_time > 1'000'000'000) {
        if (server->export_ops->heartbeat != nullptr) {
            server->export_ops->heartbeat(server->export_state);
        }
        server->last_heartbeat_time = epoch_nanos_now;
    }

    // Garbage collect any connections which did not open an event ring after
    // logging in.
    client = TAILQ_FIRST(&server->clients);
    while (client != nullptr) {
        if (client->exported_rings > 0) {
            client = TAILQ_NEXT(client, next);
            continue;
        }
        no_open_elapsed_nanos = epoch_nanos_now - client->connect_epoch_nanos;
        if (no_open_elapsed_nanos > NO_OPEN_TIMEOUT_NANOS) {
            zombie_client = client;
            client = TAILQ_NEXT(client, next);
            close_client_err(
                zombie_client,
                ETIMEDOUT,
                "client did not open a event ring after %lu seconds",
                no_open_elapsed_nanos / 1'000'000'000UL);
        }
        else {
            client = TAILQ_NEXT(client, next);
        }
    }
    if (rings_exported != nullptr) {
        *rings_exported = (unsigned)(server->export_count - exports_before);
    }
    return 0;
}
