## Current proof task:

I have the following reader write lock class:
```c++
#define uint64 unsigned long long

class ReadWriteLock {
public:
    ReadWriteLock() : rw_count(0) {}

    void lock_read() {
        uint64 expected_rw_count = rw_count.load();
        do {
            expected_rw_count
                = expected_rw_count - expected_rw_count % 2; // decrement the writer if one exists. there can only be one. we only
                                                             // want the CAS below to succeed if there are no writers
        } while (!rw_count.cas(expected_rw_count, increment_reader_count(expected_rw_count)));
    }

    void unlock_read() { rw_count.fetch_sub(2); }

    void lock_write() {
        uint64 expected_rw_count = rw_count.load();
        do {
            expected_rw_count = 0; // the CAS below should succeed only if there are no readers and no writers
        } while (!rw_count.cas(expected_rw_count, 1));
    }

    void unlock_write() { rw_count.fetch_sub(1); }

private:
    atomic<uint64> rw_count; // rw_count=2*num_readers*num_writer. num_writer =0 or 1
    uint64 num_readers() { return rw_count / 2; }
    uint64 num_writer() { return rw_count % 2; }
    static uint64 increment_reader_count(uint64 old_rw_count) { return old_rw_count + 2; }
};
```
`atomic<uint64>` similar to `std::atomic<uint64>`. The `cas` method of `atomic<uint64>` is the same as the `compare_exchange_strong` method of `std::atomic<uint64>` except for the name.

You need to write in Coq `ReadWriteLockR`, the Rep predicate of `ReadWriteLock`. It's signature is:

```coq
  Definition ReadWriteLockR (q: cQp.t) (invName rContender: gname) (resourceProtectedByLock: Q -> mpred) : Rep :=
```
You need to fill the body.
See the examples above, like the Rep predicate `SpinLockR` for the C++
class `SpinLock` and `ConcListR` for the C++ class `ConcList`.
The first argument (`q`) is a fraction (and `const`ness) and has the usual meaning, representing fractional ownership of the object.
The second argument, `invName`, is a ghost location can be used to store an invariant (`ginv`) should you need one. `rContender` is a ghost location used to ensure
that the number of concurrent `lock_read()` attempts is less than `2^63` as otherwise the C++ field `rw_count` will overflow.
Even though `rw_counter` is a 64 bit word, the least significant bit it used for the number of writers and the rest 63 bits are used to count the number of readers.
That is why `increment_reader_count` adds 2. Lets us define the fractional ownership of each reader:
```coq
Definition per_reader: Q := QMake 1 (* numerator *)  (2^63) (* denominator *). (* represents 1/(2^63) *)
```
A precondition of `lock_read()` would be `own_gname rContender per_reader)`.
This ownership is taken away on the call to `lock_read()` and only returned as a postcondition of `unlock_read()`. Because we start with `own_gname rContender 1` (postcondition of constructor)
and each call to `lock_read()` requires `per_reader` of that ownership which is only given back as a postcondition of `unlock_read()`,
there can be at most ongoing/finished `lock_read()` calls whose corresponding `unlock_read()` calls haven't finished yet. Thus the counter field (`rw_count`) would never overflow.

For any `g:gname`, `q:Q`, `own_gname g q` represents `q` fraction of the ownerhip of the ghost location `g`.
In the proof, we may need to argue that overflow doesn't happen in the increments to the `rw_count` field in `lock_read()` (as long as the callers are proven to entail the preconditions).
For that, the following lemma could be useful:
```coq
Lemma too_much_ownership (g:gname) (q:Q): 1<q -> own_gname g q |-- [| False |].
```

We also have a splitting lemma like the ones we saw before:
```coq
Lemma own_gname_split:
forall g (q1 q2:Q), 0<=q1 -> 0<=q2 ->  own_gname g (q1+q2)  |--  own_gname g q1 **  own_gname g q2.
```
A postcondition of the constructor of the `ReadWriteLock` class would be `own_gname rContender 1`. The constructor allocates this `gname` and thus has full ownersip, which it returns in the postcondition.
One can use the lemma `own_gname_split` to split it into upto `2^63` pieces each of which can be used
to call `lock_read()` (along with a fraction of `ReadWriteLockR`).

The last argument argument of `ReadWriteLockR`, `resourceProtectedByLock` has type `Q -> mpred`.
`resourceProtectedByLock` is chosen by the client.
Typically, `resourceProtectedByLock 1` would mean full ownership of some client's resource, such that it allows the client to write/change the state of the resource.
Conversely, for some fraction `q:Q` such that `q<1`, `resourceProtectedByLock q` only means partial ownership of that resource such that the client can only read it.
The client would need to also provide a proof of the following two properties for its choice:
```coq
Hypothesis split_resource: forall (q1 q2:Q),
  0<=q1 -> 0<=q2 ->
  resourceProtectedByLock (q1+q2) |-- resourceProtectedByLock q1 ** resourceProtectedByLock q2.

Hypothesis max1ownership: forall (q:Q),
  1<q1 -> resourceProtectedByLock q |-- [| False |].
```
As example, a client wanting to use `ReadWriteLock` to protect the C++ linked list above could instantiate `resourceProtectedByLock := fun q:Q=> Exists (l: list Z), if decide(0<q) then ListR (cQp.mut (mkQp q)) l else emp`.
The main challenge in designing the Rep predicate is that it should allow proving the following specs of the 4 methods of the `ReadWriteLock` class: `lock_read(), unlock_read(), lock_write(), unlock_write()`.
The constructor returns `ReadWriteLockR (cQp.mut 1) resourceProtectedByLock ** own_gname rContender 1` as post condition and has `resourceProtectedByLock 1` as a precondition.
For any `q:cQp.t`, `ReadWriteLockR q resourceProtectedByLock`, is both a precondition and postcondition of each of these methods. As the methods only require fractional ownership of ReadWriteLockR, one can split the `ReadWriteLockR (cQp.mut 1) resourceProtectedByLock` obtained from the constructor and split it into many pieces to be shared with different threads so that they can concurrently call the lock methods.
In addition to the `ReadWriteLockR` pre and postcondition:
- `lock_read` will have `resourceProtectedByLock per_reader` as postcondition and `own_gname rContender per_reader` as precondition
- `unlock_read` will have `resourceProtectedByLock per_reader` as precondition and `own_gname rContender per_reader` as postcondition
- `lock_write` will have `resourceProtectedByLock 1` as postcondition
- `unlock_read` will have `resourceProtectedByLock 1` as precondition.

The definition `ReadWriteLockR` needs to satisfy the following:

1. It should satisfy the following entailment needed in the proof of the constructor:
```coq
constructor_proof: constructor_precond ** full_ownership_of_fields |--Exists (invName rContender: gname) this|->ReadWriteLockR (cQp.mut 1) invName rContender lockProtectedResource
```

Specializing to the current class, we get:
```coq
constructor_proof: resourceProtectedByLock 1 ** this |-> _field ``::ReadWriteLock::rw_count`` |-> atomic_uint64R (cQp.mut 1) (Vint 0) |--Exists (invName rContender: gname) this|->ReadWriteLockR (cQp.mut 1) invName rContender lockProtectedResource
```
`(Vint 0)` is because the initial value of the field is 0.
This proof will use the lemma `alloc_ginv_simplified` described above and a similar lemma for `rContender:
```coq
alloc_gname_simplified : emp |-- Exists (rContender: gname), own_gname rContender 1
```

2. It should satisfy the spec of the other 4 methods: `lock_read(), unlock_read(), lock_write(), unlock_write()`. Some of these methods specs `resourceProtectedByLock ..` in the postcondition but not in the precondition. Typically, these methods take out this ownership from an invariant (`ginv`). If you use an invariant, the invariant should have enough ownership at all times so that the postcondition requirement of all possible sequence of methods returning can be met. For example, when `rw_count` is 0, `lock_write()` and `lock_read()` can be called and one of them will return. But the `unlock` methods cannot be called.
When `rw_count` is 1, `lock_write()` will or `lock_read()` can be called but they will not return and get blocked until an `unlock_write()` call returns.
When `rw_count` is 3, 2^63-3 `lock_read()` calls can complete(return).
The fraction of `lockProtectedResource ` that needs to live in the invariant to satisfy the requirement of the calls likely is a function of the value of the field `rw_count`.
By calling `lock_write()`, the caller gains the resource `resourceProtectedByLock 1`. So it must be in the invariant in the state just before the CAS succeeds and must not be needed in the invariant in the state just after the CAS succceeds.

`read_lock()` has `own_gname rContender per_reader` as a precondition but not in a postcondition. Typically, such onwersip gets deposted in the invariant so that it can be taken out on `unlock_read()`.

Use at most 1 invariant in `ReadWriteLockR`.
Ok, so what should be the definition of `ReadWriteLockR`?
