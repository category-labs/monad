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

mod pooling_allocator;
mod ptr;

use std::{fmt, ptr as raw_ptr};

use futures::channel::oneshot;
use tracing::error;

pub use self::{
    pooling_allocator::{
        ConcurrentObjectPool, LentLease, PoolLease, PoolStats, StaleTicket, Ticket,
    },
    ptr::RpcPtr,
};
use crate::ffi;

/// The FFI result descriptor owned by the store.
pub type RpcData = ffi::monad_executor_result;

// Transparent, so a pooled node's payload address is its descriptor address.
#[repr(transparent)]
struct StoredResult {
    data: RpcData,
}

// The reservation transfers exclusive access, including ownership of buffers.
// C++ allocates these buffers with allocators that permit cross-thread cleanup.
unsafe impl Send for StoredResult {}
// Shared access only exposes the descriptor; dereferencing its pointers is unsafe.
// Rust cannot access a lent result, so foreign writes exclude Rust access.
unsafe impl Sync for StoredResult {}

/// Owns fixed-capacity executor result storage shared by outstanding leases.
///
/// Constructed by the RPC stack and borrowed by
/// [`MonadExecutor`](crate::MonadExecutor), so the store outlives the C++
/// executor that completes its handles, and stale or duplicate completions are
/// always checked against live storage.
///
/// Protocol violations never crash the process: a rejected handle is logged,
/// and a result that foreign code may still access is quarantined, never
/// reused, permanently reducing the available capacity. Both are counted in
/// [`RpcStore::stats`] for alerting.
pub struct RpcStore {
    results: ConcurrentObjectPool<StoredResult>,
}

impl RpcStore {
    /// Creates empty results. Panics if `capacity` is zero.
    pub fn new(capacity: usize) -> Self {
        let empty = || StoredResult {
            data: RpcData {
                status_code: 0,
                gas_used: 0,
                gas_refund: 0,
                output_data: raw_ptr::null_mut(),
                output_data_len: 0,
                message: raw_ptr::null_mut(),
                encoded_trace: raw_ptr::null_mut(),
                encoded_trace_len: 0,
            },
        };
        // The pool recycles a result only after foreign access has ended.
        let clear = |result: &mut StoredResult| unsafe {
            ffi::monad_executor_result_clear(&mut result.data);
        };

        Self {
            results: ConcurrentObjectPool::new(capacity, empty, clear),
        }
    }

    /// Tries to reserve a result without waiting. A failed scan returns `None`.
    pub fn try_acquire(&self) -> Option<ResultLease> {
        self.results
            .try_acquire()
            .map(|lease| ResultLease { lease })
    }

    /// Returns the fixed number of results.
    pub fn capacity(&self) -> usize {
        self.results.capacity()
    }

    /// Scans the results for an approximate point-in-time snapshot.
    pub fn stats(&self) -> RpcStoreStats {
        let PoolStats {
            capacity,
            in_use,
            quarantined,
            rejected_tickets,
        } = self.results.stats();
        RpcStoreStats {
            capacity,
            in_use,
            quarantined,
            rejected_handles: rejected_tickets,
        }
    }
}

/// Result store health, for metrics and alerting.
///
/// Nonzero `quarantined` or `rejected_handles` values indicate executor
/// completion-protocol violations.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct RpcStoreStats {
    pub capacity: usize,
    /// Results reserved by requests, including those lent to the executor.
    pub in_use: usize,
    /// Results permanently withdrawn, reducing capacity until restart.
    pub quarantined: usize,
    /// Executor result handles rejected as stale, duplicate, or quarantined.
    pub rejected_handles: u64,
}

impl fmt::Debug for RpcStore {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RpcStore")
            .field("capacity", &self.capacity())
            .finish_non_exhaustive()
    }
}

/// Keeps a result reserved through foreign execution, interpretation, and the
/// final transport write. Dropping it clears the result and releases its node,
/// including for abandoned or cancelled results.
#[must_use = "retain the lease until all foreign and transport access has ended"]
pub struct ResultLease {
    lease: PoolLease<StoredResult>,
}

impl ResultLease {
    /// Lends the result to foreign code for one execution.
    ///
    /// Returns the delivery context for the executor callback, the handle to
    /// pass to foreign code, and the receiver for the completed result.
    pub fn lend(self) -> (ResultDelivery, ResultHandle, oneshot::Receiver<Self>) {
        let (lease, ticket) = self.lease.lend();
        let (sender, receiver) = oneshot::channel();
        let delivery = ResultDelivery(Some(PendingDelivery { lease, sender }));
        (delivery, ResultHandle(ticket), receiver)
    }

    /// Borrows the result after foreign writes have completed.
    pub fn result(&self) -> &RpcData {
        &self.lease.data
    }

    /// Clears the result and releases its node after the final consumer is done.
    pub fn finish(self) {
        drop(self);
    }
}

struct PendingDelivery {
    lease: LentLease<StoredResult>,
    sender: oneshot::Sender<ResultLease>,
}

impl PendingDelivery {
    fn finish(self, deliver: bool) {
        let Self { lease, sender } = self;
        match lease.reclaim() {
            Ok(lease) if deliver => {
                // A cancelled receiver returns the lease, and dropping it
                // clears and recycles the result.
                if let Err(lease) = sender.send(ResultLease { lease }) {
                    drop(lease);
                }
            }
            Ok(lease) => drop(lease),
            Err(lent) => {
                error!(
                    "executor result {} before its handle was redeemed; quarantining it",
                    if deliver { "completed" } else { "dropped" },
                );
                drop(lent);
            }
        }
    }
}

/// Owns a lent result until an operation-specific executor callback delivers it.
///
/// The callback must redeem the result's handle before recovering this
/// delivery from its context, then call [`ResultDelivery::complete`]. If the
/// handle has not been redeemed when the delivery is completed or dropped,
/// foreign code may still access the result, so it is quarantined and the
/// receiver observes cancellation.
#[must_use = "retain the delivery context until foreign execution has completed"]
pub struct ResultDelivery(Option<PendingDelivery>);

impl ResultDelivery {
    /// Delivers the result after its handle has been redeemed.
    ///
    /// If the receiver was cancelled, the result is cleared and recycled here.
    /// Otherwise the channel or consumer retains it until its final use. The
    /// result may be recycled before this method returns.
    pub fn complete(mut self) {
        if let Some(pending) = self.0.take() {
            pending.finish(true);
        }
    }
}

impl Drop for ResultDelivery {
    fn drop(&mut self) {
        if let Some(pending) = self.0.take() {
            pending.finish(false);
        }
    }
}

/// Lends a pooled result to foreign code for one execution.
///
/// It has the C layout `{ monad_executor_result *result; uint64_t generation; }`.
/// The completion callback must redeem it before recovering any per-request
/// context: a rejected handle may accompany freed or unrelated context, which
/// must be left untouched.
#[repr(transparent)]
#[must_use = "pass the handle to foreign code or redeem it"]
pub struct ResultHandle(Ticket<StoredResult>);

impl ResultHandle {
    /// Returns the result pointer for foreign code to populate.
    pub fn result_ptr(&self) -> *mut RpcData {
        self.0.as_ptr().cast()
    }

    pub fn generation(&self) -> u64 {
        self.0.generation()
    }

    /// Ends foreign access to the result, allowing its delivery to complete.
    ///
    /// Fails if the handle was already redeemed, belongs to an earlier lending
    /// of its result, or its result was quarantined. A failure logs an error,
    /// is counted in [`RpcStoreStats::rejected_handles`], and changes no
    /// lending. Success implies the handle's delivery is still alive.
    ///
    /// # Safety
    ///
    /// The handle, or the handle it was copied from, must come from
    /// [`ResultLease::lend`] on a store whose storage is still alive. Foreign
    /// code must have finished all access to the result and its nested
    /// allocations.
    pub unsafe fn redeem(self) -> Result<(), StaleTicket> {
        unsafe { self.0.redeem() }.inspect_err(|stale| {
            error!(?stale, "rejected stale or duplicate executor result handle");
        })
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::HashSet,
        ffi::c_void,
        mem::{align_of, size_of},
        ptr::{self, NonNull},
        sync::Barrier,
        thread,
    };

    use super::*;

    fn assert_empty(data: &RpcData) {
        assert_eq!(data.status_code, 0);
        assert_eq!(data.gas_used, 0);
        assert_eq!(data.gas_refund, 0);
        assert!(data.output_data.is_null());
        assert_eq!(data.output_data_len, 0);
        assert!(data.message.is_null());
        assert!(data.encoded_trace.is_null());
        assert_eq!(data.encoded_trace_len, 0);
    }

    // Simulates foreign code retaining a bitwise copy of a handle it was given.
    fn foreign_copy(handle: &ResultHandle) -> ResultHandle {
        // `ResultHandle` owns nothing, so a bitwise copy only duplicates its identity.
        unsafe { ptr::read(handle) }
    }

    // Simulates foreign code populating a lent result.
    fn write_gas_used(handle: &ResultHandle, gas_used: i64) {
        unsafe {
            (*handle.result_ptr()).gas_used = gas_used;
        }
    }

    struct CallbackContext {
        delivery: ResultDelivery,
    }

    // The intended shape of an executor completion callback.
    unsafe extern "C" fn complete_callback(handle: ResultHandle, user: *mut c_void) {
        // A rejected handle may accompany freed or unrelated context, so
        // `user` is recovered only after redemption succeeds.
        if unsafe { handle.redeem() }.is_err() {
            return;
        }
        let context = unsafe { Box::from_raw(user.cast::<CallbackContext>()) };
        context.delivery.complete();
    }

    // Lends the result and transfers its delivery into a callback context.
    fn submit(
        lease: ResultLease,
    ) -> (ResultHandle, RpcPtr<c_void>, oneshot::Receiver<ResultLease>) {
        let (delivery, handle, receiver) = lease.lend();
        let context = Box::into_raw(Box::new(CallbackContext { delivery }));
        let user = NonNull::new(context).unwrap().cast();
        (handle, RpcPtr::new(user), receiver)
    }

    #[test]
    #[should_panic(expected = "object pool capacity must be greater than zero")]
    fn zero_capacity_is_rejected() {
        RpcStore::new(0);
    }

    #[test]
    fn capacity_is_reported() {
        let store = RpcStore::new(3);
        assert_eq!(store.capacity(), 3);
        assert_eq!(format!("{store:?}"), "RpcStore { capacity: 3, .. }");
    }

    #[test]
    fn capacity_is_reserved_until_finish_or_drop() {
        let store = RpcStore::new(2);
        let first = store.try_acquire().unwrap();
        let second = store.try_acquire().unwrap();
        assert_empty(first.result());
        assert_empty(second.result());
        assert!(store.try_acquire().is_none());

        first.finish();
        let replacement = store.try_acquire().unwrap();
        assert!(store.try_acquire().is_none());
        drop(second);
        assert!(store.try_acquire().is_some());
        drop(replacement);
    }

    #[test]
    fn handle_has_c_layout() {
        #[repr(C)]
        struct CHandle {
            result: *mut RpcData,
            generation: u64,
        }

        assert_eq!(size_of::<ResultHandle>(), size_of::<CHandle>());
        assert_eq!(align_of::<ResultHandle>(), align_of::<CHandle>());

        let store = RpcStore::new(1);
        let (_delivery, handle, _receiver) = store.try_acquire().unwrap().lend();
        let raw = unsafe { std::mem::transmute::<ResultHandle, CHandle>(foreign_copy(&handle)) };
        assert_eq!(raw.result, handle.result_ptr());
        assert_eq!(raw.generation, handle.generation());
        unsafe { handle.redeem() }.unwrap();
    }

    #[test]
    fn finish_clears_result_without_moving_it() {
        let store = RpcStore::new(1);
        let (delivery, handle, mut receiver) = store.try_acquire().unwrap().lend();
        let address = handle.result_ptr().cast_const();
        // Simulate foreign writes while the result is lent.
        unsafe {
            (*handle.result_ptr()).status_code = 3;
            (*handle.result_ptr()).gas_used = 42;
            (*handle.result_ptr()).gas_refund = 7;
            handle.redeem().unwrap();
        }
        delivery.complete();
        let lease = receiver.try_recv().unwrap().unwrap();
        assert_eq!(lease.result().gas_used, 42);
        lease.finish();

        let lease = store.try_acquire().unwrap();
        assert_eq!(ptr::from_ref(lease.result()), address);
        assert_empty(lease.result());
    }

    #[test]
    fn each_request_lends_under_a_new_generation() {
        let store = RpcStore::new(1);
        let mut generations = HashSet::new();
        for _ in 0..3 {
            let (delivery, handle, receiver) = store.try_acquire().unwrap().lend();
            assert!(generations.insert(handle.generation()));
            unsafe { handle.redeem() }.unwrap();
            delivery.complete();
            drop(receiver);
        }
    }

    #[test]
    fn lease_outlives_store_and_moves_between_threads() {
        let store = RpcStore::new(1);
        let lease = store.try_acquire().unwrap();
        drop(store);
        thread::spawn(move || {
            assert_empty(lease.result());
            lease.finish();
        })
        .join()
        .unwrap();
    }

    #[test]
    fn cancelled_delivery_releases_result() {
        let store = RpcStore::new(1);
        let (delivery, handle, receiver) = store.try_acquire().unwrap().lend();
        write_gas_used(&handle, 42);
        drop(receiver);
        unsafe { handle.redeem() }.unwrap();
        assert!(store.try_acquire().is_none());
        delivery.complete();
        assert_empty(store.try_acquire().unwrap().result());
    }

    #[test]
    fn queued_result_is_cleared_when_receiver_is_dropped() {
        let store = RpcStore::new(1);
        let (delivery, handle, receiver) = store.try_acquire().unwrap().lend();
        write_gas_used(&handle, 42);
        unsafe { handle.redeem() }.unwrap();
        delivery.complete();
        assert!(store.try_acquire().is_none());
        drop(receiver);
        assert_empty(store.try_acquire().unwrap().result());
    }

    #[test]
    fn completed_delivery_retains_result_until_consumer_finishes() {
        let store = RpcStore::new(1);
        let (delivery, handle, mut receiver) = store.try_acquire().unwrap().lend();
        assert!(receiver.try_recv().unwrap().is_none());
        let address = handle.result_ptr().cast_const();
        write_gas_used(&handle, 42);
        unsafe { handle.redeem() }.unwrap();

        delivery.complete();
        assert!(store.try_acquire().is_none());
        let lease = receiver.try_recv().unwrap().unwrap();
        assert_eq!(ptr::from_ref(lease.result()), address);
        assert_eq!(lease.result().gas_used, 42);
        assert!(store.try_acquire().is_none());

        lease.finish();
        assert_empty(store.try_acquire().unwrap().result());
    }

    #[test]
    fn dropping_a_redeemed_delivery_cancels_receiver_and_clears_result() {
        let store = RpcStore::new(1);
        let (delivery, handle, mut receiver) = store.try_acquire().unwrap().lend();
        write_gas_used(&handle, 42);
        unsafe { handle.redeem() }.unwrap();

        drop(delivery);
        assert!(receiver.try_recv().is_err());
        assert_empty(store.try_acquire().unwrap().result());
    }

    #[test]
    fn callback_completes_on_another_thread_after_store_is_dropped() {
        let store = RpcStore::new(1);
        let (handle, user, mut receiver) = submit(store.try_acquire().unwrap());
        drop(store);

        thread::spawn(move || {
            write_gas_used(&handle, 42);
            unsafe { complete_callback(handle, user.as_ptr()) };
        })
        .join()
        .unwrap();
        let lease = receiver.try_recv().unwrap().unwrap();
        assert_eq!(lease.result().gas_used, 42);
        lease.finish();
    }

    #[test]
    fn simultaneous_completion_and_cancellation_release_result() {
        let store = RpcStore::new(1);

        for _ in 0..128 {
            let (handle, user, receiver) = submit(store.try_acquire().unwrap());
            let barrier = Barrier::new(2);

            thread::scope(|scope| {
                let barrier = &barrier;
                scope.spawn(move || {
                    write_gas_used(&handle, 42);
                    barrier.wait();
                    unsafe { complete_callback(handle, user.as_ptr()) };
                });
                barrier.wait();
                drop(receiver);
            });

            assert_empty(store.try_acquire().unwrap().result());
        }
    }

    #[test]
    fn stale_handle_from_an_earlier_request_is_rejected() {
        let store = RpcStore::new(1);
        let (delivery, handle, receiver) = store.try_acquire().unwrap().lend();
        let stale = foreign_copy(&handle);
        unsafe { handle.redeem() }.unwrap();
        delivery.complete();
        drop(receiver);

        // The next request reuses the slot under a new generation.
        let (delivery, current, mut receiver) = store.try_acquire().unwrap().lend();
        assert_eq!(stale.result_ptr(), current.result_ptr());
        assert!(unsafe { stale.redeem() }.is_err());
        assert_eq!(store.stats().rejected_handles, 1);

        write_gas_used(&current, 42);
        unsafe { current.redeem() }.unwrap();
        delivery.complete();
        assert_eq!(receiver.try_recv().unwrap().unwrap().result().gas_used, 42);
    }

    #[test]
    fn duplicate_completion_is_rejected_without_recovering_context() {
        let store = RpcStore::new(2);
        let (handle, user, mut receiver) = submit(store.try_acquire().unwrap());
        let duplicate = foreign_copy(&handle);
        unsafe { complete_callback(handle, user.as_ptr()) };
        receiver.try_recv().unwrap().unwrap().finish();

        // The duplicate arrives with another request's live context, which
        // must remain untouched.
        let (handle, user, mut receiver) = submit(store.try_acquire().unwrap());
        unsafe { complete_callback(duplicate, user.as_ptr()) };
        assert!(receiver.try_recv().unwrap().is_none());

        write_gas_used(&handle, 42);
        unsafe { complete_callback(handle, user.as_ptr()) };
        assert_eq!(receiver.try_recv().unwrap().unwrap().result().gas_used, 42);
    }

    #[test]
    fn completing_before_redemption_quarantines_result() {
        let store = RpcStore::new(1);
        let (delivery, handle, mut receiver) = store.try_acquire().unwrap().lend();
        write_gas_used(&handle, 42);
        delivery.complete();
        assert!(receiver.try_recv().is_err());
        assert!(store.try_acquire().is_none());

        // Foreign code may still finish with the quarantined result, but its
        // handle is rejected.
        write_gas_used(&handle, 43);
        assert!(unsafe { handle.redeem() }.is_err());
        assert!(store.try_acquire().is_none());
        assert_eq!(
            store.stats(),
            RpcStoreStats {
                capacity: 1,
                in_use: 0,
                quarantined: 1,
                rejected_handles: 1,
            }
        );
    }

    #[test]
    fn dropping_before_redemption_quarantines_result() {
        let store = RpcStore::new(1);
        let (delivery, handle, mut receiver) = store.try_acquire().unwrap().lend();
        write_gas_used(&handle, 42);
        drop(delivery);
        assert!(receiver.try_recv().is_err());
        assert!(store.try_acquire().is_none());

        write_gas_used(&handle, 43);
        assert!(unsafe { handle.redeem() }.is_err());
        assert!(store.try_acquire().is_none());
        assert_eq!(store.stats().quarantined, 1);
    }

    #[test]
    fn quarantined_handle_cannot_recover_another_requests_context() {
        let store = RpcStore::new(2);
        let (handle, user, mut receiver) = submit(store.try_acquire().unwrap());
        // A faulty callback recovers and completes its context without
        // redeeming, quarantining the result and freeing the context.
        let context = unsafe { Box::from_raw(user.as_ptr().cast::<CallbackContext>()) };
        context.delivery.complete();
        assert!(receiver.try_recv().is_err());

        // The quarantined handle then arrives with another request's live
        // context, which must remain untouched.
        let (current, user, mut receiver) = submit(store.try_acquire().unwrap());
        unsafe { complete_callback(handle, user.as_ptr()) };
        assert!(receiver.try_recv().unwrap().is_none());

        unsafe { complete_callback(current, user.as_ptr()) };
        receiver.try_recv().unwrap().unwrap().finish();
        assert_eq!(
            store.stats(),
            RpcStoreStats {
                capacity: 2,
                in_use: 0,
                quarantined: 1,
                rejected_handles: 1,
            }
        );
    }

    #[test]
    fn stats_report_requests_in_use() {
        let store = RpcStore::new(3);
        let lease = store.try_acquire().unwrap();
        let (delivery, handle, _receiver) = store.try_acquire().unwrap().lend();
        assert_eq!(
            store.stats(),
            RpcStoreStats {
                capacity: 3,
                in_use: 2,
                ..RpcStoreStats::default()
            }
        );

        unsafe { handle.redeem() }.unwrap();
        delivery.complete();
        lease.finish();
        assert_eq!(store.stats().in_use, 1);
    }

    #[test]
    fn store_types_are_thread_safe() {
        fn assert_send_sync<T: Send + Sync>() {}
        fn assert_send<T: Send>() {}
        assert_send_sync::<RpcStore>();
        assert_send_sync::<ResultLease>();
        assert_send_sync::<ResultHandle>();
        assert_send::<ResultDelivery>();
    }
}
