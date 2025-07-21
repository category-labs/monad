# VersionStack and State versioning summary

This document summarizes how **version** works in `version_stack.hpp` and how it drives nested EVM call snapshots in `state.hpp`.

## 1. VersionStack<T> (version_stack.hpp)

- Maintains a deque of `(version, T)` pairs for snapshotting values.
- `current(version)`: if `version` increased, forks (copies) the top `T` into a new slot tagged with `version`.
- `pop_accept(version)`: if the top slot matches `version`, merges or decrements the version to commit changes.
- `pop_reject(version)`: if the top slot matches `version`, pops it to roll back the snapshot.

## 2. State version_ counter (state.hpp)

- Holds `unsigned version_{0}` representing the current snapshot ID.
- `push()`: increments `version_` to start a new nested version (e.g. on entering a sub‑call or contract creation).
- `pop_accept()`: iterates over all `VersionStack` instances (accounts, logs, etc.), calls `pop_accept(version_)` to commit changes, then decrements `version_`.
- `pop_reject()`: iterates and calls `pop_reject(version_)` to revert changes, removes any newly created entries, then decrements `version_`.

## 3. EVM executor integration (evm.cpp)

- Before executing a CALL or CREATE, `state.push()` is called.
- On successful return, `state.pop_accept()` commits the snapshot.
- On failure (revert or OOG), `state.pop_reject()` rolls back state and logs.

## 4. original_ vs current_ consistency

- Whenever `current_` gains an entry for an address, it always calls `original_account_state(address)` first, which creates (if needed) an entry in `original_`.  Hence `current_` never contains an address absent from `original_`.

## Conclusion

The **version** parameter is a snapshot identifier used by `VersionStack` to fork, commit, or revert per-account state and logs in lock-step with nested EVM calls. Although it increments and decrements in sync with callchain nesting, conceptually it is a generic version tag rather than strictly the call depth.
