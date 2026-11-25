# Monad mainnet replay fixtures

`build_fixtures.py` turns real Monad mainnet blocks into blockchain-test
fixtures, using only the public RPC.

Each fixture holds one block, the pre-state its transactions touch
(`prestateTracer`), the post-state (`diffMode`) and the two preceding blocks,
whose senders feed the reserve balance checks. The `_replay` key tells
`monad-ethereum-test` that the state is partial: it skips the state root, but
still compares receipts, logs, gas and every touched account.

```console
$ python3 scripts/mainnet-replay/build_fixtures.py ~/replay --count 300
$ build/test/ethereum_test/monad-ethereum-test --blockchain-tests ~/replay
```

Blocks are sampled uniformly from the last two weeks (`--span`, `--seed`), or
given with `--blocks`. Each block takes about 6 RPC calls and 3 MB. Set
`--network` to the revision the blocks ran under (default `MONAD_TEN`).
