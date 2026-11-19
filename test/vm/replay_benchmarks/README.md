# Replay benchmarks

Times whole-block execution of real Monad mainnet blocks, in the interpreter
and the compiler. Fixtures are the `_replay` blockchain tests that
`monad-ethereum-test` runs in CI (`build/src/MonadMainnetReplayFixtures`).

```console
$ MONAD_REPLAY_FIXTURES=build/src/MonadMainnetReplayFixtures taskset -c 8,9 \
    build/test/vm/replay_benchmarks/replay-benchmarks
```

Each case (`replay/monad_mainnet_<block>/<interpreter|compiler>`) executes its
block once to compile contracts and check logs and gas, then times execution on
fresh block state. `MONAD_REPLAY_THREADS` and `MONAD_REPLAY_FIBERS` set the
execution pool (default 1).
