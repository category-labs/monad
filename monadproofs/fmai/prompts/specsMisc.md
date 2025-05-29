### Opacity of Rep predicates for clients
The definitions of the class `Rep` predicates are often supposed to be opaque to the callers of the class: the proofs of the callers of methods of a class are often not allowed to unfold the definitions of the class `Rep` predicates: they can only be unfolded in the proofs of the methods of the class (and perhaps some other friend classes).
As a part of a logical interface for the class, the clients of the class can be provided with some lemmas about the `Rep` predicate(s) of the class, in addition to the specs of the methods.
This allows the class writer to change the implementation (e.g. even change the fields) and yet guarantee that none of the proofs of callersof the functions/methods wouuld break. For example, we can make `ListR` opaque to the clients and instead expose the following decomposition lemmas along witht he spec. 

Now, if we change change the c++ implmentation of List to be an array instead of a linked list, none of the client proofs would break because the exact same specs and lemmas can also be proven for an array implementation of `ListR`. But if a client proof unfolds `ListR` to see that it is defined via `NodeR` those proofs would break if once changes to arrays.

Morally, very often, the specs should be considered as existentially quantified on the definition of the Rep predicates, from the point of the view of the proofs of callers. However, actually doing this parametrization and quanficication can make things a bit unwieldy in Coq, so we just use opacity (e.g. `Opaque ListR`) in all client proofs.

While writing the specs, it is important to think about what details can be hidden from the client and what must be exposed to the clients via specs of public methods and (often equational) lemmas about the `Rep` predicates of the class


## Multiple Rep predicates for a class
Some classes have multiple `Rep` predicates, especially in concurrency settings: different parties may have different roles at different times. For example, in a lock class, the precondition of `unlock()` may require an extra token asserting that the lock is locked, a token that can only be obtained as a postcondition of `lock()`.

As an example, consider:
class AuthFrag {
atomic<int> foo;
read();
write(int bar);
}


## Spec Examples
TODO:
- initially copy relevant classes (also classes referred to) from cpp files to prompt (this part to be automated later)
- ask agent to define the Rep of AccountState
- add RepFor for others like addressR.
- provide map Rep already in first try.
