# Monad execution overview

## Consensus and execution

The most common kind of blockchain architecture separates the operation of a
node into two distinct components, which are typically called "consensus" and
"execution."

The consensus component gets its name from the distributed consensus algorithm
it implements; this algorithm allows the network to reach agreement about new
blocks (bundles of transactions) to be appended to the blockchain. The
execution component performs the actual transaction processing, and keeps
track of the state of the blockchain in a database.

In the Category Labs architecture, the two components are developed
separately, and live in separate source code repositories. They produce
two separate binaries, which are also called "consensus" and "execution"
throughout the documentation. These binaries typically run as Linux daemons,
and are managed as systemd services.

Although the two components are typically called "consensus" and "execution",
their source code repositories and command names are different for historical
reasons:

- The consensus repository is called [monad-bft](https://github.com/category-labs/monad-bft),
  because its distributed consensus algorithm belongs to the Byzantine Fault
  Tolerant family; the name of the consensus daemon binary is `monad-node`

- The execution repository is just called [monad](https://github.com/category-labs/monad),
  and the name of the execution daemon binary is also just `monad`

## How is execution used?

Most of the source code in this repository is compiled into a single library,
called `libmonad_execution.a` (or `libmonad_execution.so`, if you compile
using shared libraries).

This library is used in a few different ways:

1. **Stand-alone/daemon mode**: the execution daemon (source code in the
   `cmd/monad` directory) is run as a systemd service; it is small
   wrapper around the `libmonad_execution` functionality that looks for
   new blocks written to disk by the consensus daemon and executes them
   immediately, updating the local state database after successful execution

2. **Hosted mode**: the consensus daemon and the RPC server also use some
   execution APIs directly; they do this by compiling the execution library
   as a shared object (`libmonad_execution.so`), and loading it into their
   processes; they can then call execution functions directly

3. **Interactive mode**: `cmd/monad` can also be run interactively from the
   command line; this is not typically done when participating in the
   blockchain network, but it is useful for developers, e.g., to manually
   replay a sequence of blocks

The way the two daemons fit together is shown in the diagram below. It is
a simple loop that starts and ends with the consensus client:

```
                       ╔════════════════════════════════╗
                       ║                                ║      Reads new blocks
  Writes new blocks    ║         The "ledger":          ║       written by the
     proposed by   ┌──▶║ a directory on the filesystem  ║────┐ consensus daemon
   consensus peers │   ║    containing recent blocks    ║    │ and executes them
                   │   ║                                ║    │
                   │   ╚════════════════════════════════╝    │
                   │                                         │
                   │                                         ▼
   ┌─Consensus daemon──────────────┐        ┌─Execution daemon───────────────┐
   │                               │        │                                │
   │┌─────────────────────────────┐│        │ ┌────────────────────────────┐ │
   ││                             ││        │ │       runloop_monad        │ │
   ││       Monad consensus       ││        │ ├────────────────────────────┤ │
   ││          algorithm          ││        │ │                            │ │
   ││                             ││        │ │    libmonad_execution.a    │ │
   │├─────────────────────────────┤│        │ │  static library functions  │ │
   ││                             ││        │ │ (including EVM and triedb) │ │
   ││    libmonad_execution.so    ││        │ │                            │ │
   ││ (including triedb read API) ││        │ └──────────────┬─────────────┘ │
   ││                             ││        └────────────────┼───────────────┘
   │└──────────────▲──────────────┘│                         │
   └───────────────┼───────────────┘                         │
                   │                                         │
                   │                                         │
                   │  ╔════════════════════════════════╗     │
                   │  ║                                ║     │
                   │  ║     TrieDB database file:      ║     │
                   └──╣     typically a dedicated      ║◀────┘
   Hosted execution   ║       NVMe block device        ║     Execution results
   library can read   ║                                ║    (e.g., state roots)
  results from triedb ╚════════════════════════════════╝    are written to the
                                                              triedb database
```

This organization helps explain why the consensus binary is called
`monad-node`: even though a "Monad node" is really both daemons operating
together, it's clear in the diagram that execution is a local service that
provides EVM and database services to consensus.

In particular, the execution daemon has no networking of any kind, nor is it
configured with any kind of public/private key identity. The "network" identity
of a node -- and all of the related code and configuration files -- are part
of the consensus daemon. To an external observer, the consensus daemon alone
_appears_ to be "the node." In reality, during normal operation of the Monad
blockchain protocol, neither daemon can do much of anything without the other.

## Organization of the source code

The source code for `libmonad_execution` is in the `category` subdirectory.
It is organized into several components, each in its own directory:

| Directory | Contains |
| --------- | -------- |
| async     | A library for asynchronous IO using `io_uring`, used by triedb                                               |
| core      | Common functionality shared by multiple components                                                           |
| execution | High-level transaction scheduling; Ethereum utilities (e.g. RLP decoding); "glue" between triedb and the EVM |
| mpt       | The triedb database; stands for "Merkle-Patricia Trie", the central state data structure of Ethereum         |
| rpc       | `extern "C"` interface to execute a single transaction; used by the RPC server to implement `eth_call`       |
| statesync | Distributed database state synchronization protocol; an `extern "C"` interface used by consensus during sync |
| vm        | Ethereum Virtual Machine implementation (interpreter and native code compiler, with Monad extensions)        |

There is also a directory called `event`, which is not listed above. This
directory is related to the "execution event SDK", which is used by third-party
applications to consume real-time blockchain data published by execution. It
produces a separate library called `libmonad_event`, which is only meant for
third parties.

All of the execution event SDK source code is actually contained in the
`category/core/event` subdirectory, so its API is also available in the
`libmonad_execution` library. `libmonad_event` is a separate CMake target in
order to simplify the build system integration of third-party users, so that
they do not need to integrate with the much larger and complex build system
of the full execution project.
