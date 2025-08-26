// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/log_ffi.h>

#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <exception>
#include <format>
#include <memory>
#include <span>
#include <utility>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/handlers/Handler.h>

static thread_local char error_buf[1024];

struct monad_log_handler
{
    std::shared_ptr<quill::Handler> quill_handler;
};

// We can't #include <syslog.h>, it has some macros that conflict with quill
enum syslog_level : uint8_t
{
    Emergency = 0,
    Alert = 1,
    Critical = 2,
    Error = 3,
    Warning = 4,
    Notice = 5,
    Info = 6,
    Debug = 7,
};

constexpr uint8_t to_syslog_level(quill::LogLevel l)
{
    using quill::LogLevel;

    switch (l) {
    case LogLevel::Critical:
        return syslog_level::Critical;
    case LogLevel::Error:
        return syslog_level::Error;
    case LogLevel::Warning:
        return syslog_level::Warning;
    case LogLevel::Info:
        return syslog_level::Info;
    case LogLevel::Debug:
        return syslog_level::Debug;
    case LogLevel::TraceL1:
        return syslog_level::Debug + 1;
    case LogLevel::TraceL2:
        return syslog_level::Debug + 2;
    case LogLevel::TraceL3:
        return syslog_level::Debug + 3;
    default:
        return syslog_level::Alert;
    }
}

constexpr quill::LogLevel to_quill_log_level(syslog_level l)
{
    using quill::LogLevel;

    switch (std::to_underlying(l)) {
    case syslog_level::Emergency:
        [[fallthrough]];
    case syslog_level::Alert:
        [[fallthrough]];
    case syslog_level::Critical:
        return LogLevel::Critical;
    case syslog_level::Error:
        return LogLevel::Error;
    case syslog_level::Warning:
        [[fallthrough]];
    case syslog_level::Notice:
        return LogLevel::Warning;
    case syslog_level::Info:
        return LogLevel::Info;
    case syslog_level::Debug:
        return LogLevel::Debug;
    case syslog_level::Debug + 1:
        return LogLevel::TraceL1;
    case syslog_level::Debug + 2:
        return LogLevel::TraceL2;
    case syslog_level::Debug + 3:
        return LogLevel::TraceL3;
    default:
        return LogLevel::None;
    }
}

// A quill log handler that wraps quill's log message in a `monad_log` object
// and calls the registered callback function
class LogCallbackHandler : public quill::Handler
{
public:
    LogCallbackHandler(
        monad_log_write_callback *write_fn, monad_log_flush_callback *flush_fn,
        uintptr_t user)
        : write_fn_{write_fn}
        , flush_fn_{flush_fn}
        , user_{user}
    {
    }

    QUILL_ATTRIBUTE_HOT void write(
        quill::fmt_buffer_t const &log_message,
        quill::TransitEvent const &log_event) override
    {
        monad_log const log = {
            .syslog_level = to_syslog_level(log_event.log_level()),
            .message = log_message.data(),
            .message_len = log_message.size(),
        };
        write_fn_(&log, user_);
    }

    QUILL_ATTRIBUTE_HOT void flush() override
    {
        if (flush_fn_ != nullptr) {
            flush_fn_(user_);
        }
    }

private:
    monad_log_write_callback *write_fn_;
    monad_log_flush_callback *flush_fn_;
    uintptr_t user_;
};

int monad_log_handler_create(
    struct monad_log_handler **handler_p, char const *name,
    monad_log_write_callback *write_fn, monad_log_flush_callback *flush_fn,
    uintptr_t user)
{
    if (name == nullptr || std::strlen(name) == 0) {
        *std::format_to(error_buf, "invalid handler name") = '\0';
        return EINVAL;
    }
    if (write_fn == nullptr) {
        *std::format_to(error_buf, "write callback cannot be nullptr") = '\0';
        return EFAULT;
    }
    try {
        *handler_p = new monad_log_handler{
            .quill_handler = quill::create_handler<LogCallbackHandler>(
                std::string{name}, write_fn, flush_fn, user)};
    }
    catch (std::exception const &ex) {
        *std::format_to(
            error_buf,
            "exception occurred creating `{}` handler: {}",
            name,
            ex.what()) = '\0';
        return EIO;
    }
    return 0;
}

int monad_log_handler_create_stdout_handler(
    struct monad_log_handler **handler_p)
{
    *handler_p = nullptr;
    try {
        std::shared_ptr<quill::Handler> stdout_handler =
            quill::stdout_handler();
        stdout_handler->set_pattern(
            "%(time) [%(thread_id)] %(file_name):%(line_number) "
            "LOG_%(log_level)\t"
            "%(message)",
            "%Y-%m-%d %H:%M:%S.%Qns",
            quill::Timezone::GmtTime);
        *handler_p =
            new monad_log_handler{.quill_handler = std::move(stdout_handler)};
        return 0;
    }
    catch (std::exception const &ex) {
        *std::format_to(
            error_buf,
            "exception occurred creating stdout handler: {}",
            ex.what()) = '\0';
        return EIO;
    }
}

void monad_log_handler_destroy(struct monad_log_handler *handler)
{
    delete handler;
}

int monad_log_init(
    struct monad_log_handler **handlers, size_t handler_count, uint8_t level)
{
    using std::chrono::duration_cast, std::chrono::nanoseconds,
        std::chrono::microseconds;

    // quill recognizes three trace levels, which are assigned after debug;
    // these aren't real syslog levels but we recognize them in case the
    // caller wants to coax quill into tracing
    if (level > syslog_level::Debug + 3) {
        *std::format_to(
            error_buf, "level {} out of syslog level range", level) = '\0';
        return ERANGE;
    }
    quill::Config cfg;
    quill::LogLevel const quill_level =
        to_quill_log_level(static_cast<syslog_level>(level));
    if (quill_level >= quill::LogLevel::Warning) {
        // Quill is designed for high performance logging, which is potentially
        // important if we're producing a lot of messages. If the logging is
        // well-behaved, it should only ever be noisy in the case of debug or
        // trace messages (perhaps also INFO). In the current configuration,
        // the caller only wants to see warnings and up; we'll allow the
        // background thread to sleep for much longer, so we don't schedule
        // it too often; we are worried about wasting limited CPU resources,
        // not the queue overflowing
        cfg.backend_thread_sleep_duration =
            duration_cast<nanoseconds>(microseconds{250});
    }
    for (monad_log_handler *h : std::span{handlers, handler_count}) {
        cfg.default_handlers.emplace_back(h->quill_handler);
    }
    try {
        quill::configure(cfg);
        quill::start(false);
        quill::get_root_logger()->set_log_level(quill_level);
    }
    catch (std::exception const &ex) {
        *std::format_to(
            error_buf,
            "exception occurred initializing logger: {}",
            ex.what()) = '\0';
        return EIO;
    }
    return 0;
}

char const *monad_log_get_last_error()
{
    return error_buf;
}
