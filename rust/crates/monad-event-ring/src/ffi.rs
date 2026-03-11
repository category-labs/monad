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

//! This module contains low-level bindings to the monad execution client event ring library. This
//! is **not** a regular Rust module and is mostly hidden.

use std::{
    ffi::{CStr, CString},
    os::fd::{AsRawFd, FromRawFd},
    path::{Path, PathBuf},
};

pub(crate) use self::bindings::{
    g_monad_event_content_type_names, monad_event_iter_result, MONAD_EVENT_CONTENT_TYPE_COUNT,
    MONAD_EVENT_CONTENT_TYPE_NONE, MONAD_EVENT_GAP, MONAD_EVENT_NOT_READY, MONAD_EVENT_SUCCESS,
};
pub use self::bindings::{
    monad_event_content_type, monad_event_descriptor, monad_event_iterator,
    monad_event_record_error, monad_event_ring, MONAD_EVENT_CONTENT_TYPE_EXEC,
    MONAD_EVENT_CONTENT_TYPE_TEST,
};

#[allow(dead_code, missing_docs, non_camel_case_types, non_upper_case_globals)]
mod bindings {
    use libc::{off_t, pid_t};

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

#[inline]
fn get_last_ring_library_error(r: libc::c_int) -> Result<(), String> {
    if r == 0 {
        return Ok(());
    }

    let err_str = unsafe {
        CStr::from_ptr(self::bindings::monad_event_ring_get_last_error())
            .to_str()
            .unwrap_or("Invalid UTF-8 in monad_event_ring_get_last_error")
    };

    Err(String::from(err_str))
}

#[inline]
fn error_name_to_cstring(str_ref: impl AsRef<str>) -> Result<CString, String> {
    CString::new(str_ref.as_ref()).map_err(|nul_err| nul_err.to_string())
}

pub(crate) fn monad_event_ring_mmap(
    mmap_prot: libc::c_int,
    mmap_extra_flags: libc::c_int,
    ring_fd: libc::c_int,
    ring_offset: libc::off_t,
    error_name: &str,
) -> Result<monad_event_ring, String> {
    let mut c_event_ring: monad_event_ring = unsafe { std::mem::zeroed() };

    let error_name_cstring = error_name_to_cstring(error_name)?;

    let r = unsafe {
        self::bindings::monad_event_ring_mmap(
            &mut c_event_ring,
            mmap_prot,
            mmap_extra_flags,
            ring_fd,
            ring_offset,
            error_name_cstring.as_ptr(),
        )
    };

    get_last_ring_library_error(r).map(|()| c_event_ring)
}

pub(crate) fn monad_event_ring_check_content_type(
    c_event_ring: &monad_event_ring,
    c_event_content_type: monad_event_content_type,
    schema_hash: &[u8; 32],
) -> Result<(), String> {
    let r = unsafe {
        self::bindings::monad_event_ring_check_content_type(
            c_event_ring,
            c_event_content_type,
            schema_hash.as_ptr(),
        )
    };

    get_last_ring_library_error(r)
}

pub(crate) fn monad_event_ring_unmap(c_event_ring: &mut monad_event_ring) {
    unsafe {
        self::bindings::monad_event_ring_unmap(c_event_ring);
    }
}

pub(crate) fn monad_event_ring_iterator_init(
    c_event_ring: &monad_event_ring,
) -> Result<monad_event_iterator, String> {
    let mut c_event_iterator: monad_event_iterator = unsafe { std::mem::zeroed() };

    let r = unsafe {
        self::bindings::monad_event_ring_init_iterator(c_event_ring, &mut c_event_iterator)
    };

    get_last_ring_library_error(r).map(|()| c_event_iterator)
}

#[inline]
pub(crate) fn monad_event_iterator_try_next(
    c_event_iterator: &mut monad_event_iterator,
) -> (monad_event_iter_result, monad_event_descriptor) {
    let mut c_event_descriptor: monad_event_descriptor = unsafe { std::mem::zeroed() };

    let c_event_iter_result: monad_event_iter_result = unsafe {
        self::bindings::monad_event_iterator_try_next(c_event_iterator, &mut c_event_descriptor)
    };

    (c_event_iter_result, c_event_descriptor)
}

pub(crate) fn monad_event_iterator_reset(c_event_iterator: &mut monad_event_iterator) {
    unsafe { self::bindings::monad_event_iterator_reset(c_event_iterator) };
}

#[inline]
pub(crate) fn monad_event_ring_payload_peek<'ring>(
    c_event_ring: &'ring monad_event_ring,
    c_event_descriptor: &monad_event_descriptor,
) -> Option<&'ring [u8]> {
    let payload_ptr = unsafe {
        self::bindings::monad_event_ring_payload_peek(c_event_ring, c_event_descriptor) as *const u8
    };

    if payload_ptr.is_null() {
        return None;
    }

    Some(unsafe {
        std::slice::from_raw_parts(payload_ptr, c_event_descriptor.payload_size as usize)
    })
}

#[inline]
pub(crate) fn monad_event_ring_payload_check(
    c_event_ring: &monad_event_ring,
    c_event_descriptor: &monad_event_descriptor,
) -> bool {
    unsafe { self::bindings::monad_event_ring_payload_check(c_event_ring, c_event_descriptor) }
}

pub(crate) fn monad_event_resolve_ring_path(input: impl AsRef<Path>) -> Result<PathBuf, String> {
    monad_event_resolve_ring_path_with_basepath(Option::<PathBuf>::None, input)
}

pub(crate) fn monad_event_resolve_ring_path_with_basepath(
    default_path: Option<impl AsRef<Path>>,
    input: impl AsRef<Path>,
) -> Result<PathBuf, String> {
    let default_path = match &default_path {
        Some(default_path) => Some(default_path.as_ref().to_str().ok_or(format!(
            "cannot extract path bytes from `{:?}`",
            input.as_ref()
        ))?),
        None => None,
    };

    let input = input.as_ref().to_str().ok_or(format!(
        "cannot extract path bytes from `{:?}`",
        input.as_ref()
    ))?;

    _monad_event_resolve_ring_path(default_path, input)
}

#[inline]
fn _monad_event_resolve_ring_path(
    default_path: Option<&str>,
    input: &str,
) -> Result<PathBuf, String> {
    let opt_default_path_cstring = match default_path {
        Some(default_path) => Some(CString::new(default_path).map_err(|e| e.to_string())?),
        None => None,
    };

    let input_cstring = CString::new(input).map_err(|e| e.to_string())?;

    let mut pathbuf_cstr_bytes = vec![0u8; libc::PATH_MAX as usize];

    let r = unsafe {
        self::bindings::monad_event_resolve_ring_file(
            opt_default_path_cstring.map_or(std::ptr::null(), |c| c.as_ptr()),
            input_cstring.as_ptr(),
            pathbuf_cstr_bytes.as_mut_ptr() as *mut libc::c_char,
            pathbuf_cstr_bytes.len(),
        )
    };

    get_last_ring_library_error(r)?;

    let pathbuf_cstr = match CStr::from_bytes_until_nul(pathbuf_cstr_bytes.as_slice()) {
        Ok(cstr) => cstr,
        Err(err) => return Err(err.to_string()),
    };

    let pathbuf_str = pathbuf_cstr
        .to_str()
        .map_err(|utf_err| utf_err.to_string())?;

    Ok(PathBuf::from(pathbuf_str))
}

pub(crate) fn monad_event_is_snapshot_file(
    file: &std::fs::File,
    error_name: impl AsRef<str>,
) -> Result<bool, String> {
    let mut is_snapshot = false;

    let error_name_cstring = error_name_to_cstring(error_name)?;

    let r = unsafe {
        self::bindings::monad_event_is_snapshot_file(
            file.as_raw_fd(),
            error_name_cstring.as_ptr(),
            &mut is_snapshot,
        )
    };

    get_last_ring_library_error(r).map(|()| is_snapshot)
}

pub(crate) fn monad_event_decompress_snapshot_fd(
    file: &std::fs::File,
    max_size: Option<usize>,
    error_name: impl AsRef<str>,
) -> Result<Option<std::fs::File>, String> {
    let error_name_cstring = error_name_to_cstring(error_name)?;

    let mut fd: libc::c_int = -1;

    let r = unsafe {
        self::bindings::monad_event_decompress_snapshot_fd(
            file.as_raw_fd(),
            max_size.unwrap_or_default(),
            error_name_cstring.as_ptr(),
            &mut fd,
        )
    };

    handle_error_and_produce_file(fd, r)
}

pub(crate) fn monad_event_decompress_snapshot_mem(
    bytes: &[u8],
    max_size: Option<usize>,
    error_name: impl AsRef<str>,
) -> Result<Option<std::fs::File>, String> {
    let error_name_cstring = error_name_to_cstring(error_name)?;

    let mut fd: libc::c_int = -1;

    let r = unsafe {
        self::bindings::monad_event_decompress_snapshot_mem(
            bytes.as_ptr() as *const ::std::os::raw::c_void,
            bytes.len(),
            max_size.unwrap_or(0),
            error_name_cstring.as_ptr(),
            &mut fd,
        )
    };

    handle_error_and_produce_file(fd, r)
}

fn handle_error_and_produce_file(
    fd: libc::c_int,
    r: libc::c_int,
) -> Result<Option<std::fs::File>, String> {
    get_last_ring_library_error(r)?;

    if fd == -1 {
        return Ok(None);
    }

    assert!(fd >= 0);

    Ok(Some(unsafe { std::fs::File::from_raw_fd(fd) }))
}
