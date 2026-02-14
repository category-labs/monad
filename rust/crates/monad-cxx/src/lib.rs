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

use std::{ffi, sync::OnceLock};

use tracing::{event, Level};

#[allow(non_camel_case_types)]
#[repr(C)]
struct monad_log {
    syslog_level: u8,
    message: *const ffi::c_char,
    message_len: usize,
}

#[allow(non_camel_case_types)]
type c_write_fn = extern "C" fn(*const monad_log, usize);

#[allow(non_camel_case_types)]
type c_flush_fn = extern "C" fn(usize);

// Called back by C++, sent to tracing framework via the event! macro
extern "C" fn log_callback(plog: *const monad_log, _: usize) {
    let log = unsafe { &*plog };
    let message_bytes =
        unsafe { std::slice::from_raw_parts(log.message as *const u8, log.message_len) };
    let message = String::from_utf8_lossy(message_bytes);
    match log.syslog_level {
        0..=3 => event!(Level::ERROR, %message),
        4 => event!(Level::WARN, %message),
        5 => event!(Level::INFO, %message),
        6 => event!(Level::DEBUG, %message),
        _ => event!(Level::TRACE, %message),
    };
}

extern "C" {
    fn monad_log_handler_create(
        handler: *const *mut ffi::c_void,
        name: *const ffi::c_char,
        write: c_write_fn,
        flush: Option<c_flush_fn>,
        user: usize,
    ) -> ffi::c_int;

    fn monad_log_handler_destroy(handler: *const ffi::c_void);

    fn monad_log_init(
        handlers: *const *const ffi::c_void,
        handler_length: usize,
        syslog_level: u8,
    ) -> ffi::c_int;

    fn monad_log_get_last_error() -> *const ffi::c_char;
}

fn check_log_library_error(rc: ffi::c_int) -> Result<(), String> {
    if rc != 0 {
        let err_str = unsafe {
            ffi::CStr::from_ptr(monad_log_get_last_error())
                .to_str() // Convert to a &str
                .unwrap_or("monad_log_get_last_error returned string with non-UTF8 chars")
        };
        Err(String::from(err_str))
    } else {
        Ok(())
    }
}

struct LogHandler {
    c_handle: *mut ffi::c_void,
}

// it's safe to call monad_log_handler_create and monad_log_destroy on different threads
unsafe impl Send for LogHandler {}
unsafe impl Sync for LogHandler {}

impl LogHandler {
    fn create(
        name: &str,
        write: c_write_fn,
        flush_opt: Option<c_flush_fn>,
        user: usize,
    ) -> Result<LogHandler, String> {
        let c_handle: *mut ffi::c_void = std::ptr::null_mut();
        let c_name_buf = match ffi::CString::new(name) {
            Ok(cstr) => cstr,
            Err(err) => return Err(err.to_string()),
        };
        let rc = unsafe {
            monad_log_handler_create(&c_handle, c_name_buf.as_ptr(), write, flush_opt, user)
        };
        check_log_library_error(rc)?;
        Ok(LogHandler { c_handle })
    }
}

impl Drop for LogHandler {
    fn drop(&mut self) {
        unsafe { monad_log_handler_destroy(self.c_handle) }
    }
}

static SINGLETON_LOG_HANDLER: OnceLock<LogHandler> = OnceLock::new();

pub fn init_cxx_logging(log_level: Level) {
    let _: &LogHandler = SINGLETON_LOG_HANDLER.get_or_init(|| {
        let handler = match LogHandler::create("cxx_to_rust", log_callback, None, 0) {
            Ok(h) => h,
            Err(e) => panic!("cannot create C++ log handler: {e}"),
        };
        let syslog_level: u8 = match log_level {
            Level::ERROR => 3,
            Level::WARN => 4,
            Level::INFO => 5,
            Level::DEBUG => 6,
            Level::TRACE => 7,
        };
        let handler_array: [*const ffi::c_void; 1] = [handler.c_handle];
        let rc = unsafe { monad_log_init(handler_array.as_ptr(), 1, syslog_level) };
        if let Err(e) = check_log_library_error(rc) {
            panic!("monad_init_log failed: {e}");
        }
        handler
    });
}
