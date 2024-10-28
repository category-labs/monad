#include <errno.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbit.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>

#include <poll.h>
#include <sys/epoll.h>
#include <sys/queue.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>

#include <monad/core/assert.h>
#include <monad/core/keccak.h>
#include <monad/core/spinlock.h>
#include <monad/core/srcloc.h>
#include <monad/event/event.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_server.h>
#include <monad/event/event_session.h>
#include <monad/event/event_shared.h>

#ifdef NDEBUG
static uint64_t const NO_SESSION_TIMEOUT_NANOS = 5'000'000'000;
#else
static uint64_t const NO_SESSION_TIMEOUT_NANOS = 60'000'000'000;
#endif

// Client of the event server, connected over a socket; this owns a list of
// open sessions
struct monad_event_client
{
    int sock_fd;
    unsigned client_id;
    struct monad_event_server *server;
    struct monad_event_session *session;
    struct sockaddr_un sock_addr;
    TAILQ_ENTRY(monad_event_client) next;
    uint64_t connect_epoch_nanos;
};

// Resources for the event server
struct monad_event_server
{
    int sock_fd;
    int epoll_fd;
    TAILQ_HEAD(, monad_event_client) active_clients;
    TAILQ_HEAD(, monad_event_client) free_clients;
    struct monad_event_client clients[MONAD_EVENT_MAX_SESSIONS];
    uint64_t last_heartbeat_time;
    struct monad_event_server_options create_options;
    struct sockaddr_un server_addr;
};

// Union of all message structures that the client might send to the server
union monad_event_client_msg
{
    enum monad_event_msg_type msg_type;

    struct
    {
        struct monad_event_open_session_msg open_session;
        struct monad_event_client_domain_info domain_info_buf[64];
    };
    struct monad_event_set_domain_mask_msg set_domain_mask;
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

static atomic_uint g_last_client_id = 1;

// Send a SESSION_ERROR message to the client explaining why the server could
// not open the session or is terminating it, then call close_client
__attribute__((format(printf, 3, 4))) static void close_client_err(
    struct monad_event_client *client, int error, char const *format, ...);

/*
 * Session management functions
 */

static void export_shared_memory_to_client(struct monad_event_client *client)
{
    union
    {
        char buf[CMSG_SPACE(sizeof(int))];
        struct cmsghdr hdr;
    } cmsg;
    struct monad_event_session_success_msg msg;
    struct iovec msg_iov[1] = {[0] = {.iov_base = &msg, .iov_len = sizeof msg}};
    struct msghdr mhdr = {
        .msg_name = nullptr,
        .msg_namelen = 0,
        .msg_iov = msg_iov,
        .msg_iovlen = 1,
        .msg_control = cmsg.buf,
        .msg_controllen = sizeof cmsg,
        .msg_flags = 0};
    struct monad_event_session *session = client->session;
    struct monad_event_payload_page_pool *page_pool =
        &g_monad_event_recorder.payload_page_pool;
    unsigned nmsgs = 0;

    cmsg.hdr.cmsg_level = SOL_SOCKET;
    cmsg.hdr.cmsg_type = SCM_RIGHTS;
    cmsg.hdr.cmsg_len = CMSG_LEN(sizeof(int));

    // Export the ring control file descriptor
    memset(&msg, 0, sizeof msg);
    msg.msg_type = MONAD_EVENT_MSG_MAP_RING_CONTROL;
    msg.ring_capacity = session->event_ring.capacity;
    msg.recorder_domain_mask = atomic_load_explicit(
        &g_monad_event_recorder.domain_enable_mask, memory_order_acquire);
    msg.effective_domain_mask =
        msg.recorder_domain_mask &
        atomic_load_explicit(
            &client->session->domain_mask, memory_order_acquire);
    *(int *)CMSG_DATA(&cmsg.hdr) = session->event_ring.control_fd;

    if (sendmsg(client->sock_fd, &mhdr, 0) == -1) {
        return close_client_err(
            client,
            errno,
            "unable to export session ring control fd for %u:%hhu",
            client->client_id,
            session->session_id);
    }
    nmsgs++;

    // Export the descriptor table file descriptor
    msg.msg_type = MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE;
    *(int *)CMSG_DATA(&cmsg.hdr) = session->event_ring.descriptor_table_fd;

    if (sendmsg(client->sock_fd, &mhdr, 0) == -1) {
        return close_client_err(
            client,
            errno,
            "unable to export session descriptor table fd %u:%hhu",
            client->client_id,
            session->session_id);
    }
    nmsgs++;

    // Export all payload page file descriptors
    msg.msg_type = MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE;
    MONAD_SPINLOCK_LOCK(&page_pool->lock);
    for (size_t p = 0;
         p < page_pool->active_page_count + page_pool->free_page_count;
         ++p) {
        *(int *)CMSG_DATA(&cmsg.hdr) = page_pool->all_pages[p]->memfd;
        if (sendmsg(client->sock_fd, &mhdr, 0) == -1) {
            MONAD_SPINLOCK_UNLOCK(&page_pool->lock);
            return close_client_err(
                client,
                errno,
                "unable to export event page %s for session %u:%hhu",
                page_pool->all_pages[p]->page_name,
                client->client_id,
                session->session_id);
        }
        nmsgs++;
    }
    MONAD_SPINLOCK_UNLOCK(&page_pool->lock);

    msg.msg_type = MONAD_EVENT_MSG_SESSION_OPEN;
    mhdr.msg_control = nullptr;
    mhdr.msg_controllen = 0;
    if (sendmsg(client->sock_fd, &mhdr, 0) == -1) {
        return close_client_err(
            client,
            errno,
            "unable to send final message for session %u:%hhu",
            client->client_id,
            session->session_id);
    }
    nmsgs++;
    WR_INFO_SRV(
        client->server,
        "exported %u memory segments for session "
        "%u:%hhu in %u messages",
        nmsgs - 1,
        client->client_id,
        session->session_id,
        nmsgs);
}

static int check_domain_metadata(
    struct monad_event_client *client,
    struct monad_event_open_session_msg const *msg)
{
    int rc;
    struct monad_event_client_domain_info const *cdi;
    struct monad_event_domain_metadata const *domain_meta;
    uint8_t keccak_buf[KECCAK256_SIZE];
    char *domain_meta_buf;
    size_t domain_meta_buf_size;
    uint64_t const recorder_mask = atomic_load_explicit(
        &g_monad_event_recorder.domain_enable_mask, memory_order_acquire);

    for (size_t d = 0; d < msg->domain_count; ++d) {
        cdi = &msg->domain_info[d];
        if ((MONAD_EVENT_DOMAIN_MASK(cdi->domain_code) & recorder_mask) == 0) {
            // Skip domains which are not enabled
            // TODO(ken): this is potentially a problem
            continue;
        }
        if (cdi->domain_code >= g_monad_event_domain_meta_size) {
            close_client_err(
                client,
                EOPNOTSUPP,
                "could not open session -- client domain code %hhu exceeds "
                "largest known value %zu in server",
                cdi->domain_code,
                g_monad_event_domain_meta_size);
            return EOPNOTSUPP;
        }
        domain_meta = &g_monad_event_domain_meta[cdi->domain_code];
        rc = monad_event_metadata_serialize(
            domain_meta, &domain_meta_buf, &domain_meta_buf_size);
        if (rc != 0) {
            close_client_err(
                client,
                EOPNOTSUPP,
                "could not open session -- metadata calculation failed for "
                "client domain %hhu, domain %s (%hhu) in the server",
                cdi->domain_code,
                domain_meta->name,
                domain_meta->domain);
            return EOPNOTSUPP;
        }
        keccak256(
            (uint8_t const *)domain_meta_buf, domain_meta_buf_size, keccak_buf);
        free(domain_meta_buf);
        if (memcmp(keccak_buf, cdi->domain_metadata_hash, sizeof keccak_buf) !=
            0) {
            close_client_err(
                client,
                EOPNOTSUPP,
                "could not open session -- metadata hash for event domain %hhu "
                "does not match server view of domain %s (%hhu)",
                cdi->domain_code,
                domain_meta->name,
                domain_meta->domain);
            return EOPNOTSUPP;
        }
    }
    return 0;
}

static void handle_open_session_msg(
    struct monad_event_client *client,
    struct monad_event_open_session_msg const *msg)
{
    int rc;
    if (check_domain_metadata(client, msg) != 0) {
        return;
    }
    if ((rc = monad_event_session_open(msg->ring_shift, &client->session)) !=
        0) {
        return close_client_err(
            client,
            rc,
            "could not open session: %s (%d)\ndetails: %s",
            strerror(rc),
            rc,
            monad_event_session_get_last_error());
    }
    WR_INFO_SRV(
        client->server,
        "opened session %u:%u with parameter ring_shift=%hhu",
        client->client_id,
        client->session->session_id,
        msg->ring_shift);
    export_shared_memory_to_client(client);
}

static void handle_set_domain_mask_msg(
    struct monad_event_client *client,
    struct monad_event_set_domain_mask_msg const *domain_mask_msg)
{
    struct monad_event_session_success_msg msg = {
        .msg_type = MONAD_EVENT_MSG_NEW_DOMAIN_MASK,
        .session_id = client->session->session_id,
        .ring_capacity = 0,
        .recorder_domain_mask = atomic_load_explicit(
            &g_monad_event_recorder.domain_enable_mask, memory_order_acquire)};
    monad_event_session_set_domain_mask(
        client->session, domain_mask_msg->domain_mask);
    msg.effective_domain_mask =
        domain_mask_msg->domain_mask & msg.recorder_domain_mask;
    if (send(client->sock_fd, &msg, sizeof msg, 0) != sizeof msg) {
        WR_ERR_SRV(
            client->server,
            errno,
            "failed to respond to event client %u changing domain mask to %lx",
            client->client_id,
            domain_mask_msg->domain_mask);
    }
}

/*
 * Client management functions
 */

static void close_client(struct monad_event_client *client)
{
    if (client->session != nullptr) {
        WR_INFO_SRV(
            client->server,
            "closing client %u triggered close of linked event session %hhu",
            client->client_id,
            client->session->session_id);
        monad_event_session_close(client->session);
        client->session = nullptr;
    }
    TAILQ_REMOVE(&client->server->active_clients, client, next);
    TAILQ_INSERT_TAIL(&client->server->free_clients, client, next);
    (void)close(client->sock_fd);
    WR_INFO_SRV(client->server, "event client %u closed", client->client_id);
}

static void close_client_err(
    struct monad_event_client *client, int error, char const *format, ...)
{
    va_list ap;
    struct monad_event_session_error_msg msg;
    size_t send_size;
    int len;
    unsigned session_id;

    msg.msg_type = MONAD_EVENT_MSG_SESSION_ERROR;
    if (client->session != nullptr) {
        msg.session_id = client->session->session_id;
    }
    msg.error_code = error;
    va_start(ap, format);
    len = vsnprintf(msg.error_buf, sizeof msg.error_buf, format, ap);
    va_end(ap);
    if (len > 0) {
        send_size = offsetof(struct monad_event_session_error_msg, error_buf) +
                    (size_t)len + 1;
        if (send(client->sock_fd, &msg, send_size, 0) == -1) {
            session_id =
                client->session != nullptr ? client->session->session_id : 0;
            WR_ERR_SRV(
                client->server,
                errno,
                "unable to send error message about dying session: %u:%d",
                client->client_id,
                session_id);
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

static void accept_client(struct monad_event_server *server)
{
    struct sockaddr_un client_addr;
    socklen_t client_addr_size = sizeof client_addr;
    struct monad_event_client *client;
    struct epoll_event evt;
    int client_fd;
    struct monad_event_session_error_msg err_msg;

    client_fd = accept4(
        server->sock_fd,
        (struct sockaddr *)&client_addr,
        &client_addr_size,
        SOCK_CLOEXEC);
    if (client_fd == -1) {
        WR_ERR_SRV(server, errno, "accept4(2) failed for next client");
        return;
    }
    client = TAILQ_FIRST(&server->free_clients);
    if (client == nullptr) {
        err_msg.msg_type = MONAD_EVENT_MSG_SESSION_ERROR;
        snprintf(
            err_msg.error_buf,
            sizeof err_msg.error_buf,
            "maximum number of clients %lu reached",
            sizeof server->clients / sizeof(struct monad_event_client));
        (void)send(client_fd, &err_msg, sizeof err_msg, 0);
        (void)close(client_fd);
        return;
    }
    TAILQ_REMOVE(&server->free_clients, client, next);

    memset(client, 0, sizeof *client);
    TAILQ_INSERT_TAIL(&server->active_clients, client, next);
    client->sock_fd = client_fd;
    client->client_id = atomic_fetch_add(&g_last_client_id, 1);
    client->server = server;
    memcpy(&client->sock_addr, &client_addr, client_addr_size);
    WR_INFO_SRV(
        server, "new connection from event client %u", client->client_id);
    client->connect_epoch_nanos = monad_event_get_epoch_nanos();

    evt.events = EPOLLIN;
    evt.data.ptr = client;
    if (epoll_ctl(server->epoll_fd, EPOLL_CTL_ADD, client_fd, &evt) == -1) {
        WR_ERR_SRV(server, errno, "epoll_ctl(2) adding client socket failed");
        close_client(client);
    }
}

/*
 * Client socket I/O functions
 */

static void handle_client_socket_read(struct monad_event_client *client)
{
    union monad_event_client_msg msg;

    if (recv(client->sock_fd, &msg, sizeof msg, 0) == -1) {
        WR_ERR_SRV(
            client->server,
            errno,
            "recv(2) from event client %u failed",
            client->client_id);
        close_client(client);
    }
    switch (msg.msg_type) {
    case MONAD_EVENT_MSG_OPEN_SESSION:
        return handle_open_session_msg(client, &msg.open_session);

    case MONAD_EVENT_MSG_SET_DOMAIN_MASK:
        return handle_set_domain_mask_msg(client, &msg.set_domain_mask);

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

int monad_event_server_create(
    struct monad_event_server_options const *options,
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
    TAILQ_INIT(&server->active_clients);
    TAILQ_INIT(&server->free_clients);
    for (unsigned c = 0;
         c < sizeof server->clients / sizeof(struct monad_event_client);
         ++c) {
        TAILQ_INSERT_TAIL(&server->free_clients, &server->clients[c], next);
    }
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
    if (listen(server->sock_fd, MONAD_EVENT_MAX_SESSIONS)) {
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
    MONAD_ASSERT(server != nullptr);
    while (!TAILQ_EMPTY(&server->active_clients)) {
        close_client(TAILQ_FIRST(&server->active_clients));
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
    sigset_t const *sigmask)
{
#define SERVER_EPOLL_EVENT_MAX 16
    uint64_t epoch_nanos_now;
    uint64_t no_session_elapsed_nanos;
    struct epoll_event events[SERVER_EPOLL_EVENT_MAX];
    struct monad_event_client *client;
    struct monad_event_client *zombie_client;
    int nready;

    if (server == nullptr) {
        return EFAULT;
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
    epoch_nanos_now = monad_event_get_epoch_nanos();
    if (epoch_nanos_now - server->last_heartbeat_time > 1'000'000'000) {
        MONAD_EVENT(MONAD_EVENT_HEARTBEAT, 0);
        server->last_heartbeat_time = epoch_nanos_now;
    }

    // Garbage collect any connections which did not open an event session
    // after logging in.
    client = TAILQ_FIRST(&server->active_clients);
    while (client != nullptr) {
        if (client->session != nullptr) {
            client = TAILQ_NEXT(client, next);
            continue;
        }
        no_session_elapsed_nanos =
            epoch_nanos_now - client->connect_epoch_nanos;
        if (no_session_elapsed_nanos > NO_SESSION_TIMEOUT_NANOS) {
            zombie_client = client;
            client = TAILQ_NEXT(client, next);
            close_client_err(
                zombie_client,
                ETIMEDOUT,
                "client did not open a session after %lu seconds",
                no_session_elapsed_nanos / 1'000'000'000UL);
        }
        else {
            client = TAILQ_NEXT(client, next);
        }
    }
    return 0;
}
