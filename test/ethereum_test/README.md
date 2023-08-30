# Ethereum Tests

This directory contains a target that parses tests from the [ethereum/tests](https://github.com/ethereum/tests) repo and
executes them using Monad's state implementation.

## Test Runner

- TODO

## Scripts

### Getting an Expected Post State from geth

You can use the following script to dump various debug state from a geth implementation.

```text
$ ./scripts/genpoststate/wrap_gps.sh
Usage: ./scripts/genpoststate/wrap_gps.sh <path_to_json_test_file> <fork_name> <transaction index>
```

#### Example

```shell
./scripts/genpoststate/wrap_gps.sh third_party/ethereum-tests/GeneralStateTests/VMTests/vmArithmeticTest/add.json Berlin 0
```

### Getting Post State from Monad

By enabling the `--ethereum-test` logger, you can simply grep for `post_state` and trim off the log prefix to get the
monad post state after running an ethereum test.

#### Example

```text
$ ./cmake-build-debug/test/ethereum_test/monad-ethereum-test \
--gtest_filter=VMTests/vmArithmeticTest.add \
--fork Berlin \
--txn 0 \
log_levels --ethereum_test debug \
| grep post_state \
| cut -d ' ' -f 19 \
| jq

```

#### Example Ouput

```json
{
    "0x03601462093b5945d1676df093446790fd31b20e7b12a2e8e5e09d068109616b": {
        "balance": "0xba1a9ce0b9aa781",
        "code": "0x",
        "nonce": "0x1"
    },
    "0x227a737497210f7cc2f464e3bfffadefa9806193ccdf873203cd91c8d3eab518": {
        "balance": "0xba1a9ce0ba1a9ce",
        "code": "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
        "nonce": "0x0",
        "storage": {
            "0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
            "original_account_address": "0x0000000000000000000000000000000000000100"
        }
    },
    "0x4599828688a5c37132b6fc04e35760b4753ce68708a7b7d4d97b940047557fdb": {
        "balance": "0xba1a9ce0ba1a9ce",
        "code": "0x60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
        "nonce": "0x0"
    },
    "0x4c933a84259efbd4fb5d1522b5255e6118da186a2c71ec5efaa5c203067690b7": {
        "balance": "0xba1a9ce0ba1a9ce",
        "code": "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60010160005500",
        "nonce": "0x0"
    },
    "0x9d860e7bb7e6b09b87ab7406933ef2980c19d7d0192d8939cf6dc6908a03305f": {
        "balance": "0x7024c",
        "code": "0x",
        "nonce": "0x0"
    },
    "0xa17eacbc25cda025e81db9c5c62868822c73ce097cee2a63e33a2e41268358a1": {
        "balance": "0xba1a9ce0ba1a9ce",
        "code": "0x60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
        "nonce": "0x0"
    },
    "0xa5cc446814c4e9060f2ecb3be03085683a83230981ca8f19d35a4438f8c2d277": {
        "balance": "0xba1a9ce0ba1a9ce",
        "code": "0x600060000160005500",
        "nonce": "0x0"
    },
    "0xf057b39b049c7df5dfa86c4b0869abe798cef059571a5a1e5bbf5168cf6c097b": {
        "balance": "0xba1a9ce0ba1a9cf",
        "code": "0x600060006000600060006004356101000162fffffff100",
        "nonce": "0x0"
    }
}
```


