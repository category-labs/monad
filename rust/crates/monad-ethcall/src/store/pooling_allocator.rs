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

use std::{
    cell::UnsafeCell,
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::{
        atomic::{AtomicU64, AtomicUsize, Ordering},
        Arc,
    },
};

use super::ptr::RpcPtr;

const PHASE_BITS: u32 = 2;
const PHASE_MASK: u64 = (1 << PHASE_BITS) - 1;
const MAX_GENERATION: u64 = u64::MAX >> PHASE_BITS;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[repr(u64)]
enum Phase {
    Free = 0,
    Leased = 1,
    Lent = 2,
    // Terminal: the lease ended while foreign code could still access the node.
    Quarantined = 3,
}

/// A node's lending generation and phase, packed into one atomic word so
/// ticket redemption can check both in a single compare-and-exchange.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct NodeState {
    generation: u64,
    phase: Phase,
}

impl NodeState {
    fn pack(self) -> u64 {
        debug_assert!(self.generation <= MAX_GENERATION);
        (self.generation << PHASE_BITS) | self.phase as u64
    }

    fn unpack(bits: u64) -> Self {
        let phase = match bits & PHASE_MASK {
            0 => Phase::Free,
            1 => Phase::Leased,
            2 => Phase::Lent,
            _ => Phase::Quarantined,
        };
        Self {
            generation: bits >> PHASE_BITS,
            phase,
        }
    }

    fn with_phase(self, phase: Phase) -> Self {
        Self { phase, ..self }
    }
}

// `data` must remain the first field: tickets recover their node from the
// payload address, and `UnsafeCell<T>` has the same layout as `T`.
#[repr(C)]
struct Node<T> {
    data: UnsafeCell<T>,
    state: AtomicU64,
    rejected_tickets: AtomicU64,
}

// Only the successful claimant can access the value, until its lease releases it.
unsafe impl<T: Send> Sync for Node<T> {}

struct PoolInner<T> {
    nodes: Box<[Node<T>]>,
    cursor: AtomicUsize,
    recycle: fn(&mut T),
}

/// A fixed-capacity pool with stable addresses and atomic, nonblocking acquisition.
///
/// Releasing a node first passes its value to `recycle`; values are otherwise
/// retained between leases.
pub struct ConcurrentObjectPool<T> {
    inner: Arc<PoolInner<T>>,
}

impl<T> ConcurrentObjectPool<T> {
    /// Initializes every node once. Panics if `capacity` is zero.
    pub fn new(capacity: usize, mut initialize: impl FnMut() -> T, recycle: fn(&mut T)) -> Self {
        assert!(
            capacity > 0,
            "object pool capacity must be greater than zero"
        );

        let free = NodeState {
            generation: 0,
            phase: Phase::Free,
        };
        let nodes = (0..capacity)
            .map(|_| Node {
                data: UnsafeCell::new(initialize()),
                state: AtomicU64::new(free.pack()),
                rejected_tickets: AtomicU64::new(0),
            })
            .collect();

        Self {
            inner: Arc::new(PoolInner {
                nodes,
                cursor: AtomicUsize::new(0),
                recycle,
            }),
        }
    }

    /// Returns the fixed number of nodes.
    pub fn capacity(&self) -> usize {
        self.inner.nodes.len()
    }

    /// Scans the nodes for an approximate point-in-time snapshot.
    pub fn stats(&self) -> PoolStats {
        let mut stats = PoolStats {
            capacity: self.capacity(),
            ..PoolStats::default()
        };
        for node in &self.inner.nodes {
            match NodeState::unpack(node.state.load(Ordering::Relaxed)).phase {
                Phase::Free => {}
                Phase::Leased | Phase::Lent => stats.in_use += 1,
                Phase::Quarantined => stats.quarantined += 1,
            }
            stats.rejected_tickets += node.rejected_tickets.load(Ordering::Relaxed);
        }
        stats
    }

    /// Returns an exclusive lease, or `None` if this scan claims no node.
    ///
    /// A failed scan does not imply all nodes were busy at one instant.
    pub fn try_acquire(&self) -> Option<PoolLease<T>> {
        let nodes = &self.inner.nodes;
        let mut index = self.inner.cursor.fetch_add(1, Ordering::Relaxed) % nodes.len();

        for _ in 0..nodes.len() {
            let state = &nodes[index].state;
            let current = state.load(Ordering::Relaxed);
            let observed = NodeState::unpack(current);
            if observed.phase == Phase::Free
                && state
                    .compare_exchange(
                        current,
                        observed.with_phase(Phase::Leased).pack(),
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    )
                    .is_ok()
            {
                return Some(PoolLease {
                    slot: Slot {
                        inner: Arc::clone(&self.inner),
                        index,
                    },
                    _marker: PhantomData,
                });
            }

            index = if index == nodes.len() - 1 {
                0
            } else {
                index + 1
            };
        }

        None
    }
}

/// Pool occupancy and ticket rejections, for metrics and alerting.
#[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
pub struct PoolStats {
    pub capacity: usize,
    /// Nodes held by a lease, including lent nodes.
    pub in_use: usize,
    /// Nodes permanently withdrawn because their lease ended while foreign
    /// code could still access them.
    pub quarantined: usize,
    /// Redemptions rejected as stale, duplicate, quarantined, or invalid.
    pub rejected_tickets: u64,
}

/// A claimed node. Dropping it recycles and frees the node, unless foreign
/// code may still access it.
struct Slot<T> {
    inner: Arc<PoolInner<T>>,
    index: usize,
}

impl<T> Slot<T> {
    fn node(&self) -> &Node<T> {
        &self.inner.nodes[self.index]
    }

    // Rust references and lent pointers both derive from a pointer to the
    // whole node, never from a `&mut T`, so a lent pointer's validity does not
    // depend on a transient Rust borrow, and tickets may address the node.
    fn data_ptr(&self) -> NonNull<T> {
        let node: *const Node<T> = self.node();
        // `node` is valid, and `UnsafeCell::raw_get` creates no reference.
        let data = UnsafeCell::raw_get(unsafe { &raw const (*node).data });
        // A pointer into an allocated node is never null.
        unsafe { NonNull::new_unchecked(data) }
    }

    fn load_state(&self) -> NodeState {
        NodeState::unpack(self.node().state.load(Ordering::Acquire))
    }
}

impl<T> Drop for Slot<T> {
    fn drop(&mut self) {
        // Only the slot's owner moves a node out of `Leased`, so a leased
        // node cannot become lent concurrently.
        let mut current = self.load_state();
        if current.phase == Phase::Lent {
            // Quarantining also makes later redemptions fail, so a redeemed
            // ticket always implies its lease is still alive.
            match self.node().state.compare_exchange(
                current.pack(),
                current.with_phase(Phase::Quarantined).pack(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // Foreign code may still access the node, so it is never
                    // recycled, and leaking the pool keeps its storage valid.
                    mem::forget(Arc::clone(&self.inner));
                    return;
                }
                // A concurrent redemption ended foreign access first.
                Err(found) => current = NodeState::unpack(found),
            }
            debug_assert_eq!(current.phase, Phase::Leased);
        }

        // The slot exclusively owns the node, and foreign access has ended.
        (self.inner.recycle)(unsafe { &mut *self.data_ptr().as_ptr() });
        self.node()
            .state
            .store(current.with_phase(Phase::Free).pack(), Ordering::Release);
    }
}

/// Exclusive access to a node's value, keeping its storage alive until
/// explicitly finished or dropped, including on cancellation.
#[must_use = "hold the lease until all consumers have finished accessing the value"]
pub struct PoolLease<T> {
    slot: Slot<T>,
    // Sharing a lease exposes &T, so unlike the pool it requires T: Sync.
    _marker: PhantomData<T>,
}

impl<T> PoolLease<T> {
    /// Lends the value to foreign code under a new generation.
    ///
    /// The returned [`LentLease`] gives no access to the value. It can be
    /// reclaimed only after the ticket is redeemed.
    pub fn lend(self) -> (LentLease<T>, Ticket<T>) {
        let Self { slot, .. } = self;
        let current = slot.load_state();
        debug_assert_eq!(current.phase, Phase::Leased);

        // Concurrent stale redemptions expect an older lent state, so they
        // cannot interleave with this transition.
        let generation = (current.generation + 1) & MAX_GENERATION;
        let lent = NodeState {
            generation,
            phase: Phase::Lent,
        };
        slot.node().state.store(lent.pack(), Ordering::Release);

        let ticket = Ticket {
            ptr: RpcPtr::new(slot.data_ptr()),
            generation,
        };
        (LentLease { slot, generation }, ticket)
    }

    /// Recycles the value and releases the node after all consumers have
    /// stopped accessing it.
    pub fn finish(self) {
        drop(self);
    }
}

impl<T> Deref for PoolLease<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // A `PoolLease` is never lent, so it exclusively owns the node.
        unsafe { self.slot.data_ptr().as_ref() }
    }
}

impl<T> DerefMut for PoolLease<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // A `PoolLease` is never lent, so it exclusively owns the node.
        unsafe { &mut *self.slot.data_ptr().as_ptr() }
    }
}

/// A lease whose value is lent to foreign code.
///
/// Dropping it before its ticket is redeemed quarantines the node: it is never
/// recycled, later redemptions of its ticket fail, and the pool storage is
/// leaked so foreign access stays valid.
#[must_use = "reclaim the lease after its ticket is redeemed"]
pub struct LentLease<T> {
    slot: Slot<T>,
    generation: u64,
}

impl<T> LentLease<T> {
    /// Returns the lease if its ticket has been redeemed, or `self` otherwise.
    pub fn reclaim(self) -> Result<PoolLease<T>, Self> {
        let redeemed = NodeState {
            generation: self.generation,
            phase: Phase::Leased,
        };
        if self.slot.load_state() != redeemed {
            return Err(self);
        }

        let Self { slot, .. } = self;
        Ok(PoolLease {
            slot,
            _marker: PhantomData,
        })
    }
}

/// Identifies one lending of a pool node to foreign code.
///
/// It has the C layout `{ T *ptr; uint64_t generation; }`, so it can be passed
/// across FFI by value and returned on completion.
#[repr(C)]
#[must_use = "a lent node cannot be reclaimed until its ticket is redeemed"]
pub struct Ticket<T> {
    ptr: RpcPtr<T>,
    generation: u64,
}

impl<T> Ticket<T> {
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    pub fn generation(&self) -> u64 {
        self.generation
    }

    /// Ends the lending identified by this ticket, allowing its lease to be
    /// reclaimed.
    ///
    /// Fails if the ticket was already redeemed, its node has since been lent
    /// again, or its lease was dropped first. A failure changes no lending and
    /// is counted in [`PoolStats::rejected_tickets`]. Succeeds at most once
    /// per lending, and only while the lending's [`LentLease`] is alive.
    ///
    /// # Safety
    ///
    /// The ticket, or the ticket it was copied from, must come from
    /// [`PoolLease::lend`] on a pool whose storage is still alive. Outstanding
    /// leases keep the storage alive; stale tickets require keeping the pool
    /// alive. All foreign access through the ticket must have ended.
    pub unsafe fn redeem(self) -> Result<(), StaleTicket> {
        // `Node` is `repr(C)` with its payload first, so both share an address.
        let node = self.ptr.as_ptr().cast::<Node<T>>().cast_const();
        // The caller guarantees the node's storage is alive. Only its atomic
        // fields are referenced, never the payload another lease may own.
        let (state, rejected_tickets) = unsafe { (&(*node).state, &(*node).rejected_tickets) };
        let reject = |found| {
            rejected_tickets.fetch_add(1, Ordering::Relaxed);
            Err(StaleTicket {
                ticket_generation: self.generation,
                node: found,
            })
        };
        if self.generation > MAX_GENERATION {
            return reject(None);
        }

        let lent = NodeState {
            generation: self.generation,
            phase: Phase::Lent,
        };
        match state.compare_exchange(
            lent.pack(),
            lent.with_phase(Phase::Leased).pack(),
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => Ok(()),
            Err(found) => reject(Some(NodeState::unpack(found))),
        }
    }
}

/// A ticket did not identify its node's current lending.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct StaleTicket {
    ticket_generation: u64,
    // `None` when the ticket's generation is out of range.
    node: Option<NodeState>,
}

#[cfg(test)]
mod tests {
    use std::{
        cell::Cell,
        ptr,
        sync::{atomic::AtomicBool, Barrier},
        thread,
    };

    use super::*;

    fn keep(_: &mut i32) {}

    fn reset(value: &mut i32) {
        *value = 0;
    }

    // Simulates foreign code retaining a bitwise copy of a ticket it was given.
    fn foreign_copy<T>(ticket: &Ticket<T>) -> Ticket<T> {
        // `Ticket` owns nothing, so a bitwise copy only duplicates its identity.
        unsafe { ptr::read(ticket) }
    }

    fn reclaimed<T>(lent: LentLease<T>) -> PoolLease<T> {
        lent.reclaim().ok().expect("ticket should be redeemed")
    }

    #[test]
    #[should_panic(expected = "object pool capacity must be greater than zero")]
    fn zero_capacity_is_rejected() {
        ConcurrentObjectPool::new(0, || (), |_| ());
    }

    #[test]
    fn exhaustion_and_release() {
        let pool = ConcurrentObjectPool::new(2, || 0, keep);
        let first = pool.try_acquire().unwrap();
        let second = pool.try_acquire().unwrap();
        assert!(pool.try_acquire().is_none());

        first.finish();
        let replacement = pool.try_acquire().unwrap();
        assert!(pool.try_acquire().is_none());
        drop(second);
        assert!(pool.try_acquire().is_some());
        drop(replacement);
    }

    #[test]
    fn reuse_preserves_value_and_address() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let mut lease = pool.try_acquire().unwrap();
        *lease = 42;
        let address = ptr::from_ref(&*lease);
        lease.finish();

        let lease = pool.try_acquire().unwrap();
        assert_eq!(*lease, 42);
        assert_eq!(ptr::from_ref(&*lease), address);
    }

    #[test]
    fn release_recycles_value() {
        let pool = ConcurrentObjectPool::new(1, || 0, reset);
        let mut lease = pool.try_acquire().unwrap();
        *lease = 42;
        lease.finish();
        assert_eq!(*pool.try_acquire().unwrap(), 0);
    }

    #[test]
    fn cursor_wraparound_still_visits_every_node() {
        let mut index = 0;
        let pool = ConcurrentObjectPool::new(
            3,
            || {
                index += 1;
                index
            },
            keep,
        );
        pool.inner.cursor.store(usize::MAX, Ordering::Relaxed);
        let leases: Vec<_> = (0..3).map(|_| pool.try_acquire().unwrap()).collect();
        assert!(pool.try_acquire().is_none());
        let mut values: Vec<_> = leases.iter().map(|lease| **lease).collect();
        values.sort_unstable();
        assert_eq!(values, [1, 2, 3]);
    }

    #[test]
    fn leases_keep_values_alive_and_drop_them_once() {
        struct Value(Arc<AtomicUsize>);

        impl Drop for Value {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }

        let drops = Arc::new(AtomicUsize::new(0));
        let pool = ConcurrentObjectPool::new(2, || Value(Arc::clone(&drops)), |_| ());
        let lease = pool.try_acquire().unwrap();
        drop(pool);
        assert_eq!(drops.load(Ordering::Relaxed), 0);
        lease.finish();
        assert_eq!(drops.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn pool_supports_send_but_not_sync_values() {
        fn assert_send_sync<T: Send + Sync>() {}
        fn assert_send<T: Send>() {}
        assert_send_sync::<ConcurrentObjectPool<Cell<usize>>>();
        assert_send::<PoolLease<Cell<usize>>>();
        assert_send_sync::<LentLease<Cell<usize>>>();
        assert_send_sync::<Ticket<Cell<usize>>>();
    }

    #[test]
    fn cancelled_receiver_returns_lease_to_sender() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let lease = pool.try_acquire().unwrap();
        let (sender, receiver) = futures::channel::oneshot::channel();
        drop(receiver);

        let Err(lease) = sender.send(lease) else {
            panic!("sending to a cancelled receiver should fail");
        };
        assert!(pool.try_acquire().is_none());
        drop(lease);
        assert!(pool.try_acquire().is_some());
    }

    #[test]
    fn dropping_queued_result_releases_lease() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let lease = pool.try_acquire().unwrap();
        let (sender, receiver) = futures::channel::oneshot::channel();

        assert!(sender.send(lease).is_ok());
        assert!(pool.try_acquire().is_none());
        drop(receiver);
        assert!(pool.try_acquire().is_some());
    }

    #[test]
    fn concurrent_claims_are_exclusive() {
        const CAPACITY: usize = 4;
        const THREADS: usize = 8;
        const ITERATIONS: usize = 1_000;

        let mut index = 0;
        let pool = ConcurrentObjectPool::new(
            CAPACITY,
            || {
                let value = (index, 0usize);
                index += 1;
                value
            },
            |_| (),
        );
        let active: [AtomicBool; CAPACITY] = std::array::from_fn(|_| AtomicBool::new(false));
        let barrier = Barrier::new(THREADS);

        thread::scope(|scope| {
            for _ in 0..THREADS {
                scope.spawn(|| {
                    barrier.wait();
                    for _ in 0..ITERATIONS {
                        let mut lease = loop {
                            if let Some(lease) = pool.try_acquire() {
                                break lease;
                            }
                            thread::yield_now();
                        };
                        let index = lease.0;
                        assert!(!active[index].swap(true, Ordering::SeqCst));
                        lease.1 += 1;
                        thread::yield_now();
                        assert!(active[index].swap(false, Ordering::SeqCst));
                        lease.finish();
                    }
                });
            }
        });

        let leases: Vec<_> = (0..CAPACITY).map(|_| pool.try_acquire().unwrap()).collect();
        assert_eq!(
            leases.iter().map(|lease| lease.1).sum::<usize>(),
            THREADS * ITERATIONS
        );
    }

    #[test]
    fn lend_redeem_and_reclaim_round_trip() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let lease = pool.try_acquire().unwrap();
        let address = ptr::from_ref(&*lease).cast_mut();
        let (lent, ticket) = lease.lend();
        assert_eq!(ticket.as_ptr(), address);

        // Simulate a foreign write while the node is lent.
        unsafe {
            *ticket.as_ptr() = 42;
            ticket.redeem().unwrap();
        }
        assert_eq!(*reclaimed(lent), 42);
    }

    #[test]
    fn reclaim_waits_for_redemption() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let (lent, ticket) = pool.try_acquire().unwrap().lend();
        let Err(lent) = lent.reclaim() else {
            panic!("an unredeemed lease should not be reclaimed");
        };
        unsafe { ticket.redeem() }.unwrap();
        reclaimed(lent).finish();
    }

    #[test]
    fn every_lending_has_a_new_generation() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let (lent, first) = pool.try_acquire().unwrap().lend();
        let first_generation = first.generation();
        unsafe { first.redeem() }.unwrap();
        let (lent, second) = reclaimed(lent).lend();
        let second_generation = second.generation();
        assert_ne!(second_generation, first_generation);
        unsafe { second.redeem() }.unwrap();
        reclaimed(lent).finish();

        let (lent, third) = pool.try_acquire().unwrap().lend();
        assert_ne!(third.generation(), first_generation);
        assert_ne!(third.generation(), second_generation);
        unsafe { third.redeem() }.unwrap();
        reclaimed(lent).finish();
    }

    #[test]
    fn duplicate_redemption_is_rejected() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let (lent, ticket) = pool.try_acquire().unwrap().lend();
        let duplicate = foreign_copy(&ticket);
        unsafe { ticket.redeem() }.unwrap();
        assert!(unsafe { duplicate.redeem() }.is_err());
        reclaimed(lent).finish();
    }

    #[test]
    fn stale_ticket_cannot_redeem_a_recycled_node() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let (lent, ticket) = pool.try_acquire().unwrap().lend();
        let stale = foreign_copy(&ticket);
        unsafe { ticket.redeem() }.unwrap();
        reclaimed(lent).finish();

        let (lent, current) = pool.try_acquire().unwrap().lend();
        assert_eq!(current.as_ptr(), stale.as_ptr());
        assert!(unsafe { stale.redeem() }.is_err());
        let Err(lent) = lent.reclaim() else {
            panic!("a stale ticket should not end the current lending");
        };
        unsafe { current.redeem() }.unwrap();
        reclaimed(lent).finish();
    }

    #[test]
    fn out_of_range_generation_is_rejected() {
        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        let (lent, ticket) = pool.try_acquire().unwrap().lend();
        // Packing would discard these high bits and match the live generation.
        let mut forged = foreign_copy(&ticket);
        forged.generation |= !MAX_GENERATION;
        assert!(unsafe { forged.redeem() }.is_err());
        let Err(lent) = lent.reclaim() else {
            panic!("a forged ticket should not end the current lending");
        };
        unsafe { ticket.redeem() }.unwrap();
        reclaimed(lent).finish();
    }

    #[test]
    fn tickets_address_their_own_nodes() {
        let pool = ConcurrentObjectPool::new(2, || 0, keep);
        let (first, first_ticket) = pool.try_acquire().unwrap().lend();
        let (second, second_ticket) = pool.try_acquire().unwrap().lend();
        // Both lendings share a generation, so only the address tells them apart.
        assert_eq!(first_ticket.generation(), second_ticket.generation());

        unsafe { second_ticket.redeem() }.unwrap();
        let Err(first) = first.reclaim() else {
            panic!("redeeming one node should not end another's lending");
        };
        reclaimed(second).finish();
        unsafe { first_ticket.redeem() }.unwrap();
        reclaimed(first).finish();
    }

    #[test]
    fn dropping_an_unredeemed_lease_quarantines_its_node() {
        let pool = ConcurrentObjectPool::new(1, || 7, reset);
        let (lent, ticket) = pool.try_acquire().unwrap().lend();
        drop(lent);
        assert!(pool.try_acquire().is_none());
        drop(pool);

        // The quarantined value is neither recycled nor freed while foreign
        // code may still access it, but its ticket can no longer be redeemed.
        unsafe {
            assert_eq!(*ticket.as_ptr(), 7);
            *ticket.as_ptr() = 42;
            assert!(ticket.redeem().is_err());
        }
    }

    #[test]
    fn stats_count_occupancy_quarantines_and_rejections() {
        let pool = ConcurrentObjectPool::new(4, || 0, keep);
        assert_eq!(
            pool.stats(),
            PoolStats {
                capacity: 4,
                ..PoolStats::default()
            }
        );

        let leased = pool.try_acquire().unwrap();
        let (lent, ticket) = pool.try_acquire().unwrap().lend();
        let (quarantined, orphaned) = pool.try_acquire().unwrap().lend();
        let duplicate = foreign_copy(&ticket);
        unsafe { ticket.redeem() }.unwrap();
        assert!(unsafe { duplicate.redeem() }.is_err());
        drop(quarantined);
        assert!(unsafe { orphaned.redeem() }.is_err());
        assert_eq!(
            pool.stats(),
            PoolStats {
                capacity: 4,
                in_use: 2,
                quarantined: 1,
                rejected_tickets: 2,
            }
        );

        drop(leased);
        reclaimed(lent).finish();
        assert_eq!(
            pool.stats(),
            PoolStats {
                capacity: 4,
                in_use: 0,
                quarantined: 1,
                rejected_tickets: 2,
            }
        );
    }

    #[test]
    fn dropping_a_redeemed_lease_recycles_its_node() {
        let pool = ConcurrentObjectPool::new(1, || 0, reset);
        let (lent, ticket) = pool.try_acquire().unwrap().lend();
        unsafe {
            *ticket.as_ptr() = 42;
            ticket.redeem().unwrap();
        }
        drop(lent);
        assert_eq!(*pool.try_acquire().unwrap(), 0);
    }

    #[test]
    fn concurrent_duplicate_redemptions_succeed_once() {
        const THREADS: usize = 8;

        let pool = ConcurrentObjectPool::new(1, || 0, keep);
        for _ in 0..64 {
            let (lent, ticket) = pool.try_acquire().unwrap().lend();
            let mut copies: Vec<_> = (1..THREADS).map(|_| foreign_copy(&ticket)).collect();
            copies.push(ticket);
            let barrier = Barrier::new(THREADS);
            let successes = AtomicUsize::new(0);

            thread::scope(|scope| {
                for copy in copies {
                    let (barrier, successes) = (&barrier, &successes);
                    scope.spawn(move || {
                        barrier.wait();
                        if unsafe { copy.redeem() }.is_ok() {
                            successes.fetch_add(1, Ordering::Relaxed);
                        }
                    });
                }
            });

            assert_eq!(successes.load(Ordering::Relaxed), 1);
            reclaimed(lent).finish();
        }
    }
}
