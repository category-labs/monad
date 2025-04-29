### Invariants
The above sharing does not work for the cases where multiple threads can race to write on a memory location, typically an atomic word. For example, in a lock implementation, multiple threads can race to write to the lock flag (e.g. a boolean).
Consider the following lock class:
```c++
class SpinLock {
public:
    SpinLock() : locked(false) {}

    void lock() {
        while (locked.exchange(true))
            ;
    }

    void unlock() { locked.store(false); }

private:
    atomic<bool> locked;
};
```
Suppose a standard Coq Rep predicated `atomic_boolR` has already be defined
for the C++ class `atomic<bool>` and it is merely a wrapper over the the underlying
boolean field of the `atomic<bool>`:
```C++
template<typename T>
class atomic {
private:
    T _n;
	...
```
for `b:bool`, `q:cQp.t`,  `atomic_boolR q b` is roughly defined as
```coq
_field ``::atomic<bool>::_n`` |-> (primR Tbool q (Vbool b))
```

For the intended use cases of locks, it would not be directly useful for clients of the `SpinLock` class to define its Rep predicate as:
```coq
Definition SpinLockR (q: cQp.t) (b: bool) : Rep :=
  structR ``::SpinLock`` q ** _field ``::SpinLock::locked`` |-> atomic_boolR q b
```
We could share this ownership between two threads, each owning
`SpinLockR (cQp.mut (1/2)) b` but then none of those threads would be able to change
the `locked` field.
For these situations (write-write concurrency, write-read concurrency), we use the concept of
concurrency invariants. The idea is to put ownership of the fields what are accessed concurrently (with some accesses being a write) into a concurency invariant. These invariants can be shared with many threads. They can all get access to the contents of the invariant, but only for one hardware-atomic action, e.g. compare_and_exchange, fetch_and_add, atomic_load, atomic_store.
To construct invariants, we have the construct `ginv: gname -> mpred -> mpred` based on definitions from the iris separation logic library in Coq.
Given `g:gname`, `P:mpred`, `ginv g P` of type `mpred` denotes an invariant that holds the resource/assertion `P` which multiple threads can access concurrently.
`g` is a ghost (logical) location storing the invariant: there can be many invariants involved in a proof, each stored at a different location.
Just like elements of type `ptr` are physical locations where C++ values of type `val` are stored,
elements of type `gname` are "ghost locations" where logical values of almost arbitrary Coq types can be stored.
Also, in the separation logic, we can talk about ownership of these ghost locations.

Under the hood `gname` is just a wrapper over the `positive` type of Coq.
There is a axiom in the separation logic allowing allocation of new invariants along with its unique id (`gname`):
```coq
alloc_ginv_simplified : forall P:mpred, P |-- Exists (newid: gname), ginv newid P
```
(The actualy lemma's statement is a bit more complex but knowing that is not essential for now *)

Just before a thread does any such atomic operation, it can open invariants.
Opening `ginv P` gives us `P`. At the end of the atomic oparation, `P` must be returned to the invariant. This return is called closing the invariant.
 crucial property of `ginv` is that it can be duplicated:
```coq
Lemma duplicate_ginv: forall (g: gname) P:mpred, ginv g P |-- ginv g P ** ginv g P.
```
Thus, multiple threads can be give access to the invariant.

With that, one way to write `SpinLockR` is:
```coq
Definition SpinLockR (q: cQp.t) (invName: gname): Rep :=
  as_Rep (fun (this:ptr)=>
     this |-> structR ``::SpinLock`` q
       ** ginv invName (Exists locked:bool,
                           this |-> _field ``::SpinLock::locked`` |-> atomic_boolR (cQp.mut 1) locked
	                      )).
```
Because `ginv` takes an `mpred`, not a `Rep`, we needed the `this |->` in `this |-> atomic_boolR 1 b`
to make it an `mpred`. Recall that Rep is morally `ptr -> mpred` (assertions relative to a pointer).
`as_Rep` injects a `ptr -> mpred` into `Rep`.

Using the `duplicate_ginv` lemma, we would be able to prove:
```coq
Lemma fracsplit_spinR: forall q1 q2, SpinLockR (q1+q2)  |--  SpinLockR q1 **  SpinLockR q2.
```
Thus, multiple threads would be able to race to call the `lock()` method which uses the atomic
compare_and_exchange operation to change the boolean `locked` field.
This definition of `SpinLockR` can be used to prove a trivial spec the SpinLock class, where
`SpinLockR` is the only precondition and the only postcondition.

But this would still not be a useful spec.
Locks are typically used to transfer ownership of non-atomic memory locations across threads.
For example, when a thread calls `lock()`, in the separation logic proof,
it typically aquires some ownership/resource (when the call to `lock()` returns) which
it returns back to the lock by calling `unlock()`.
Between a call to `unlock()` and subsequent call to `lock()` the resource needs to live somewhere
and a convenient place could be the invariant in the definition of `SpinLockR`.
In fact, in separation logic proofs, invariants (`ginv`) are the most common way to share resources across threads.
Thus, a better definition of `SpinLockR` is:
```coq
Definition SpinLockR (q: cQp.t) (invName: gname) (lockProtectedResource: mpred) : Rep :=
  as_Rep (fun (this:ptr)=>
     this |-> structR ``::SpinLock`` q
       ** ginv invName (Exists locked:bool,
                           this |-> _field ``::SpinLock::locked`` |-> atomic_boolR (cQp.mut 1) locked
	                     ** if locked then lockProtectedResource else emp
	                      )).
```


The parameter `lockProtectedResource:mpred` is the resource that the lock protects.
This argument specified by caller to the constructor of the class `SpinLock`.
The postcondition of the constructor would be `this|->SpinLockR (cQp.mut 1) lockProtectedResource` and the precondition would be `lockProtectedResource`.
The constructor proof takes the precondition and puts it into the invariant when the constructor sets `locked:=false`.
Here `this:ptr` is the memory location of the object on which the method is being called.
`

This resource stays in the invariant in `SpinLockR` when the lock
is not locked, as formalized in this part of the definition of `SpinLockR`:
```coq
	if locked then emp else lockProtectedResource
```
The call to `lock()` only returns when `locked` goes to `true` from `false` in a compare_and_exchange operation.
Before that atomic operation `lockProtectedResource` was in the invariant but after that operation, the invariant needs to be closed by returning the invariant resource (specified as argument to `ginv`) back to the invariant.
Because ``locked:=true` after the operation, `lockProtectedResource` does not need to be in the invariant anymore (`if locked then emp else lockProtectedResource` becomes `emp`) so the thread gets to keep it in the proof
and thus `lockProtectedResource` can be returned to the caller of `lock()` as a postcondition.
In general, invariants stores the resources that threads can take out by calling methods.
After somebody has taken a lock, they own `lockProtectedResource` so it is not at the invariant at that time.
When the thread calls `unlock()`, the ownership is deposited
back to the invariant, waiting for the next caller of `lock()` to take it out.

Conversely, `lockProtectedResource` is a precondition to `unlock()` and the proof of `unlock` puts this back into the invariant when setting `locked` to `true`.
In addition to that, `this|->SpinLockR q lockProtectedResource` is both a precondition and postcondition to the `lock()` and `unlock()` methods. Note both the methods can be called with any fractional permission (`q` need not be the full fraction (cQp.mut 1)).

The constructor allocates the invariant, typically at the end of the constructor body, so we need to prove:
```coq
constructor_proof: constructor_precond ** full_ownership_of_fields |-- Exists invName:gname, this|->SpinLockR (cQp.mut 1) invName lockProtectedResource
```
Lets look at the constructor again:
```c++
    SpinLock() : locked(false) {}
```
Its precondition is `lockProtectedResource`.  At the end, locked:=false.
Unfolding definitions we need to prove:
```coq
lockProtectedResource |-- this |-> _field ``::SpinLock::locked`` |-> atomic_boolR (cQp.mut 1) false |-- Exists (invName: gname),
     this |-> structR ``::SpinLock`` q
       ** ginv invName (Exists locked:bool,
                           this |-> _field ``::SpinLock::locked`` |-> atomic_boolR (cQp.mut 1) locked
	                     ** if locked then lockProtectedResource else emp
	                      ).
```
This can be proven easily by using the `alloc_ginv_simplified` lemma above. The quantification `Exists locked:bool` needs to be instantiated with `false`.

To illustrate a concrete example usecase of `SpinLockedR`, consider the following implementation of a concurrent list which wraps the linked list we saw earlier
with a lock so that the linked list operations can be done from multiple threads concurrently:
```c++
class ConcList {
    void reverse() {
        sp.lock();
        list = ::reverse(list);
        sp.unlock();
    }
    unsigned long length() {
        sp.lock();
        auto l = ::length(list);
        sp.unlock();
        return l;
    }

private:
    SpinLock sp;
    List list{null};
};
```
We can define the Rep predicate of `ConcListR` as follows:
```coq
Definition ConcListR (q: cQp.t) (invName: gname) :=
  as_Rep (fun (this:ptr)=>
     this |-> structR ``::ConcList`` q
       ** this |-> _field `::ConcList::sp`
       |->  SpinLockR q invName (
         Exists (l: list Z) (lloc: ptr),
           this |-> _field `::ConcList::list` |-> primR (Tptr (Tnamed ``::Node``)) (cQp.mut q) (Vptr lloc) **
           lloc |-> ListR (cQp. mut 1) l
    )).
```
We have instantiated the `lockProtectedResource` of `SpinLockR` as the ownership of the entire linked list at the `::ConcList::list` field (full ownership of all the memory locations involved in the linked list).
The default constructor of `ConcList` will have the postcondition:
```coq
Exists (invName:gname), ConcListR (cQp.mut 1) invName
```

The thread invoking the constructor can then use the following easily probable lemma to split the 1 fraction in two pieces (e.g.  `ConcListR (cQp.mut 1/2) invName`) and share it 2 threads so that they can concurrently read/change the list:
```coq
Lemma fracsplit_concR: forall invName q1 q2, ConcListR (q1+q2) invName  |--  ConcListR q1 invName **  ConcListR q2 invName.
```
Both pieces of ConcListR will have a reference to the invariant `invName` and the invariant itself contains the full ownership of the linked list. The thread who succeeds at `sp.lock()` gets full ownership of the linked list and can safely modify it. Note that the linked-list data structure itself does not use any atomic memory locations: it is protected by the SpinLock.
