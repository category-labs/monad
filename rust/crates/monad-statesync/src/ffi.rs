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

pub use self::bindings::{
    monad_statesync_client, monad_statesync_client_context, monad_statesync_client_handle_done,
    monad_statesync_client_handle_target, monad_statesync_client_handle_upsert, monad_sync_done,
    monad_sync_request, monad_sync_type_SYNC_TYPE_DONE, monad_sync_type_SYNC_TYPE_REQUEST,
    monad_sync_type_SYNC_TYPE_TARGET, monad_sync_type_SYNC_TYPE_UPSERT_ACCOUNT,
    monad_sync_type_SYNC_TYPE_UPSERT_ACCOUNT_DELETE, monad_sync_type_SYNC_TYPE_UPSERT_CODE,
    monad_sync_type_SYNC_TYPE_UPSERT_HEADER, monad_sync_type_SYNC_TYPE_UPSERT_STORAGE,
    monad_sync_type_SYNC_TYPE_UPSERT_STORAGE_DELETE,
};

#[allow(dead_code, non_camel_case_types, non_upper_case_globals)]
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

pub type StateSyncContext = Box<dyn FnMut(monad_sync_request)>;

// void (*statesync_send_request)(struct StateSync *, struct SyncRequest)
#[no_mangle]
pub extern "C" fn statesync_send_request(
    statesync: *mut monad_statesync_client,
    request: monad_sync_request,
) {
    let statesync = statesync as *mut StateSyncContext;
    unsafe { (*statesync)(request) }
}

fn add_client_prefixes_as_new_peers(ctx: *mut monad_statesync_client_context, client_version: u32) {
    let prefixes = unsafe { self::bindings::monad_statesync_client_prefixes() };

    for prefix in 0..prefixes {
        unsafe {
            self::bindings::monad_statesync_client_handle_new_peer(
                ctx,
                prefix as u64,
                client_version,
            )
        }
    }
}

/// Thin unsafe wrapper around statesync_client_context that handles destruction and finalization
/// checking
pub struct StateSyncCtx {
    dbname_paths: *const *const ::std::os::raw::c_char,
    len: usize,
    sq_thread_cpu: Option<::std::os::raw::c_uint>,
    request_ctx: StateSyncContext,
    statesync_send_request: ::std::option::Option<
        unsafe extern "C" fn(arg1: *mut monad_statesync_client, arg2: monad_sync_request),
    >,
    client_version: u32,

    ctx: Option<*mut monad_statesync_client_context>,
}

impl StateSyncCtx {
    /// Initialize StateSyncCtx. There should only ever be *one* StateSyncCtx at any given time.
    pub fn new(
        dbname_paths: *const *const ::std::os::raw::c_char,
        len: usize,
        sq_thread_cpu: Option<::std::os::raw::c_uint>,
        request_ctx: StateSyncContext,
        statesync_send_request: ::std::option::Option<
            unsafe extern "C" fn(arg1: *mut monad_statesync_client, arg2: monad_sync_request),
        >,
    ) -> Self {
        let client_version = unsafe { bindings::monad_statesync_version() };
        assert!(unsafe { bindings::monad_statesync_client_compatible(client_version) });

        Self {
            dbname_paths,
            len,
            sq_thread_cpu,
            request_ctx,
            statesync_send_request,
            client_version,

            ctx: None,
        }
    }

    pub fn get_ctx(&self) -> Option<*mut monad_statesync_client_context> {
        self.ctx
    }

    pub fn get_or_create_ctx(&mut self) -> *mut monad_statesync_client_context {
        *self.ctx.get_or_insert_with(|| unsafe {
            self::bindings::monad_statesync_client_context_create(
                self.dbname_paths,
                self.len,
                self.sq_thread_cpu
                    .unwrap_or(self::bindings::MONAD_SQPOLL_DISABLED),
                (&mut self.request_ctx as *mut StateSyncContext).cast(),
                self.statesync_send_request,
            )
        })
    }

    pub fn get_or_create_ctx_with_client_prefixes(
        &mut self,
    ) -> *mut monad_statesync_client_context {
        *self.ctx.get_or_insert_with(|| unsafe {
            let ctx = self::bindings::monad_statesync_client_context_create(
                self.dbname_paths,
                self.len,
                self.sq_thread_cpu
                    .unwrap_or(self::bindings::MONAD_SQPOLL_DISABLED),
                (&mut self.request_ctx as *mut StateSyncContext).cast(),
                self.statesync_send_request,
            );

            add_client_prefixes_as_new_peers(ctx, self.client_version);

            ctx
        })
    }

    pub fn add_client_prefixes_as_new_peers(&mut self) {
        let ctx = self.ctx.expect(
            "add_client_prefixes_as_new_peers should only be called on active StateSyncCtx",
        );

        add_client_prefixes_as_new_peers(ctx, self.client_version);
    }

    pub fn has_reached_target(&mut self) -> bool {
        let ctx = self
            .ctx
            .expect("has_reached_target should only be called on active StateSyncCtx");

        unsafe { self::bindings::monad_statesync_client_has_reached_target(ctx) }
    }

    // Returns true when the root matches
    pub fn finalize(&mut self) -> bool {
        let ctx = self
            .ctx
            .take()
            .expect("finalize should only be called on active StateSyncCtx");

        let root_matches = unsafe { self::bindings::monad_statesync_client_finalize(ctx) };

        unsafe {
            self::bindings::monad_statesync_client_context_destroy(ctx);
        }

        root_matches
    }
}
