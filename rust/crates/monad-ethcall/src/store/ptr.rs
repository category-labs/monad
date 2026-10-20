// Copyright (C) 2025-26 Category Labs, Inc.
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

use core::ptr::NonNull;

/// A non-owning, non-null pointer to an RPC resource shared with foreign code.
///
/// It does not take ownership or extend the pointee's lifetime.
#[repr(transparent)]
pub struct RpcPtr<T>(NonNull<T>);

// An `RpcPtr` only carries an address, so moving or sharing it never accesses
// `T`. Every dereference is unsafe and must itself establish exclusive or
// synchronized access, including any thread-safety `T` requires.
unsafe impl<T> Send for RpcPtr<T> {}
unsafe impl<T> Sync for RpcPtr<T> {}

impl<T> RpcPtr<T> {
    /// Creates a new `RpcPtr` from a non-null raw pointer.
    pub fn new(ptr: NonNull<T>) -> Self {
        Self(ptr)
    }

    pub fn as_ptr(&self) -> *mut T {
        self.0.as_ptr()
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::Cell, mem::size_of};

    use super::*;

    #[test]
    fn rpc_ptr_is_send_sync_for_thread_unsafe_payloads() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<RpcPtr<*mut u8>>();
        assert_send_sync::<RpcPtr<Cell<u8>>>();
    }

    #[test]
    fn rpc_ptr_size() {
        assert_eq!(size_of::<RpcPtr<u8>>(), size_of::<*mut u8>());
    }

    #[test]
    fn rpc_ptr_preserves_address() {
        let mut value = 42;
        let ptr = NonNull::from(&mut value);
        assert_eq!(RpcPtr::new(ptr).as_ptr(), ptr.as_ptr());
    }
}
