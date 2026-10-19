# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

"""Build blockchain-test fixtures from real Monad mainnet blocks.

Each fixture holds one block, the pre-state it touches (from prestateTracer),
and the two preceding blocks so the runner can rebuild the sender and
authority sets that reserve-balance checks depend on.
"""

import argparse
import concurrent.futures
import json
import os
import random
import sys
import time
import urllib.request

DEFAULT_RPCS = [
    "https://rpc.monad.xyz",
    "https://rpc1.monad.xyz",
    "https://rpc2.monad.xyz",
]
SYSTEM_SENDER = "0x6f49a8f621353f12378d0046e7d7e4b9b249dc9e"
HISTORY_STORAGE = "0x0000f90827f1c53a10cb7a02335b175320002935"
HISTORY_SERVE_WINDOW = 8191
RIPEMD = "0x0000000000000000000000000000000000000003"
NULL_ROOT = "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
NULL_LIST_HASH = "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"


class Rpc:
    def __init__(self, urls):
        self.urls = urls
        self.next = 0

    def call(self, method, params):
        last = None
        for attempt in range(8):
            url = self.urls[self.next % len(self.urls)]
            self.next += 1
            body = json.dumps(
                {"jsonrpc": "2.0", "id": 1, "method": method, "params": params}
            ).encode()
            req = urllib.request.Request(
                url,
                data=body,
                headers={
                    "content-type": "application/json",
                    "user-agent": "monad-replay-fixtures",
                },
            )
            try:
                with urllib.request.urlopen(req, timeout=120) as r:
                    resp = json.load(r)
                if "result" in resp and resp["result"] is not None:
                    return resp["result"]
                last = resp.get("error")
            except Exception as e:
                last = e
            time.sleep(min(30, 2**attempt))
        raise RuntimeError(f"{method} {params}: {last}")


def rlp_list_header(length):
    if length < 56:
        return bytes([0xC0 + length])
    n = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([0xF7 + len(n)]) + n


def with_empty_withdrawals(block_rlp):
    """Append the empty withdrawals list that Monad block bodies omit."""
    b = bytes.fromhex(block_rlp[2:])
    if b[0] < 0xF8:
        payload = b[1:]
    else:
        payload = b[1 + b[0] - 0xF7 :]
    payload += b"\xc0"
    return "0x" + (rlp_list_header(len(payload)) + payload).hex()


def merge_prestate(prestates, diffs):
    """Union per-transaction pre-states into the state before the block.

    The first transaction that touches an account or slot sees its pre-block
    value. Accounts created and slots written from zero by an earlier
    transaction are not in that transaction's pre-state, so a later
    transaction would otherwise leak post-write values backwards.
    """
    state = {}
    seen_accounts = set()
    seen_slots = set()
    for pre, diff in zip(prestates, diffs):
        # The prestate tracer skips RIPEMD (0x03); the diff tracer doesn't.
        for addr, acct in {**diff["pre"], **pre}.items():
            if addr not in seen_accounts:
                seen_accounts.add(addr)
                state[addr] = {
                    "balance": acct.get("balance", "0x0"),
                    "nonce": hex(acct.get("nonce", 0)),
                    "code": acct.get("code", "0x"),
                    "storage": {},
                }
            if addr not in state:
                continue
            for slot, value in acct.get("storage", {}).items():
                if (addr, slot) not in seen_slots:
                    seen_slots.add((addr, slot))
                    state[addr]["storage"][slot] = value
        for addr, acct in diff["post"].items():
            seen_accounts.add(addr)
            for slot in acct.get("storage", {}):
                seen_slots.add((addr, slot))
    for addr in list(state):
        acct = state[addr]
        acct["storage"] = {k: v for k, v in acct["storage"].items() if int(v, 16) != 0}
        if (
            int(acct["balance"], 16) == 0
            and int(acct["nonce"], 16) == 0
            and acct["code"] in ("0x", "")
            and not acct["storage"]
        ):
            del state[addr]
    return state


def apply_diffs(pre, diffs):
    """Apply each transaction's diffMode delta to get the post-block state.

    A slot in an account's pre storage but not its post storage was cleared.
    An account in a delta's pre but not its post either had only slots
    cleared or was deleted. A deleted account had no code and a zero nonce:
    it was empty (EIP-161), or a contract created in the same transaction at
    a funded address self-destructed (EIP-6780). Native contracts such as
    staking have storage and a nonce but no code, so they are kept.
    """
    state = json.loads(json.dumps(pre))
    for diff in diffs:
        before, after = diff["pre"], diff["post"]
        for addr, prev in before.items():
            if addr in after:
                continue
            if prev.get("nonce", 0) == 0 and prev.get("code", "0x") in ("0x", ""):
                state.pop(addr, None)
            elif addr in state:
                for slot in prev.get("storage", {}):
                    state[addr]["storage"].pop(slot, None)
        for addr, delta in after.items():
            acct = state.setdefault(
                addr,
                {"balance": "0x0", "nonce": "0x0", "code": "0x", "storage": {}},
            )
            if "balance" in delta:
                acct["balance"] = delta["balance"]
            if "nonce" in delta:
                acct["nonce"] = hex(delta["nonce"])
            if "code" in delta:
                acct["code"] = delta["code"]
            for slot in before.get(addr, {}).get("storage", {}):
                if slot not in delta.get("storage", {}):
                    acct["storage"].pop(slot, None)
            for slot, value in delta.get("storage", {}).items():
                acct["storage"][slot] = value
    for acct in state.values():
        acct["storage"] = {k: v for k, v in acct["storage"].items() if int(v, 16) != 0}
    return state


def add_history_storage(rpc, number, pre, post):
    """Add the EIP-2935 parent hash write, which happens before any
    transaction and so is missing from per-transaction traces."""
    key = "0x%064x" % ((number - 1) % HISTORY_SERVE_WINDOW)
    parent = hex(number - 1)
    before = rpc.call("eth_getStorageAt", [HISTORY_STORAGE, key, parent])
    after = rpc.call("eth_getStorageAt", [HISTORY_STORAGE, key, hex(number)])
    if HISTORY_STORAGE not in pre:
        pre[HISTORY_STORAGE] = {
            "balance": rpc.call("eth_getBalance", [HISTORY_STORAGE, parent]),
            "nonce": rpc.call("eth_getTransactionCount", [HISTORY_STORAGE, parent]),
            "code": rpc.call("eth_getCode", [HISTORY_STORAGE, parent]),
            "storage": {},
        }
    for state, value in ((pre, before), (post, after)):
        acct = state.setdefault(
            HISTORY_STORAGE, json.loads(json.dumps(pre[HISTORY_STORAGE]))
        )
        acct["storage"].pop(key, None)
        if int(value, 16) != 0:
            acct["storage"][key] = value


def add_untraced_accounts(rpc, number, addresses, pre, post):
    """Add accounts the tracers skip (RIPEMD, the beneficiary) from the parent
    block, in case a transaction reads one without changing it."""
    parent = hex(number - 1)
    for addr in addresses:
        if addr in pre:
            continue
        acct = {
            "balance": rpc.call("eth_getBalance", [addr, parent]),
            "nonce": rpc.call("eth_getTransactionCount", [addr, parent]),
            "code": rpc.call("eth_getCode", [addr, parent]),
            "storage": {},
        }
        if (
            int(acct["balance"], 16) == 0
            and int(acct["nonce"], 16) == 0
            and acct["code"] in ("0x", "")
        ):
            continue
        pre[addr] = acct
        post.setdefault(addr, json.loads(json.dumps(acct)))


def genesis_header(parent):
    return {
        "parentHash": "0x" + "00" * 32,
        "uncleHash": NULL_LIST_HASH,
        "coinbase": parent["miner"],
        "stateRoot": parent["stateRoot"],
        "transactionsTrie": NULL_ROOT,
        "receiptTrie": NULL_ROOT,
        "bloom": "0x" + "00" * 256,
        "difficulty": "0x0",
        "number": parent["number"],
        "gasLimit": parent["gasLimit"],
        "gasUsed": "0x0",
        "timestamp": parent["timestamp"],
        "extraData": parent["extraData"],
        "mixHash": parent["mixHash"],
        "nonce": parent["nonce"],
        "baseFeePerGas": parent["baseFeePerGas"],
        "withdrawalsRoot": NULL_ROOT,
        "blobGasUsed": parent.get("blobGasUsed", "0x0"),
        "excessBlobGas": parent.get("excessBlobGas", "0x0"),
        "parentBeaconBlockRoot": parent.get("parentBeaconBlockRoot", "0x" + "00" * 32),
        "requestsHash": parent.get("requestsHash"),
        "hash": "0x" + "00" * 32,
    }


def build_fixture(rpc, number, network):
    block = rpc.call("eth_getBlockByNumber", [hex(number), False])
    parent = rpc.call("eth_getBlockByNumber", [hex(number - 1), False])
    rlps = [
        rpc.call("debug_getRawBlock", [hex(n)]) for n in range(number - 2, number + 1)
    ]
    prestates = rpc.call(
        "debug_traceBlockByNumber", [hex(number), {"tracer": "prestateTracer"}]
    )
    diffs = rpc.call(
        "debug_traceBlockByNumber",
        [hex(number), {"tracer": "prestateTracer", "tracerConfig": {"diffMode": True}}],
    )
    if len(prestates) != len(block["transactions"]) or len(diffs) != len(
        block["transactions"]
    ):
        raise RuntimeError(f"block {number}: trace/transaction count mismatch")
    pre = merge_prestate([p["result"] for p in prestates], [d["result"] for d in diffs])
    post = apply_diffs(pre, [d["result"] for d in diffs])
    add_history_storage(rpc, number, pre, post)
    add_untraced_accounts(rpc, number, [RIPEMD, block["miner"].lower()], pre, post)
    header = genesis_header(parent)
    if header["requestsHash"] is None:
        del header["requestsHash"]
    return {
        f"monad_mainnet_{number}": {
            "network": network,
            "genesisBlockHeader": header,
            "pre": pre,
            "blocks": [{"rlp": with_empty_withdrawals(rlps[2])}],
            "postState": post,
            "_replay": {
                "ancestorBlocks": rlps[:2],
                "blockHash": block["hash"],
                "timestamp": block["timestamp"],
                "transactions": len(block["transactions"]),
            },
        }
    }


def sample_blocks(rpc, count, span, seed, min_txs):
    head = int(rpc.call("eth_blockNumber", []), 16)
    rng = random.Random(seed)
    chosen = []
    tried = set()
    while len(chosen) < count:
        if len(tried) == span - 100:
            sys.exit(f"only {len(chosen)} of {count} blocks in range have {min_txs}+ txs")
        n = rng.randrange(head - span, head - 100)
        if n in tried:
            continue
        tried.add(n)
        b = rpc.call("eth_getBlockByNumber", [hex(n), True])
        users = [t for t in b["transactions"] if t["from"].lower() != SYSTEM_SENDER]
        if len(users) >= min_txs:
            chosen.append(n)
    return sorted(chosen)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("out", help="output directory (one JSON file per block)")
    ap.add_argument("--blocks", type=int, nargs="*", help="explicit block numbers")
    ap.add_argument("--count", type=int, default=300)
    ap.add_argument(
        "--span",
        type=int,
        default=3_000_000,
        help="sample from the last SPAN blocks (~2 weeks at 0.4 s)",
    )
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument(
        "--min-txs",
        type=int,
        default=1,
        help="skip blocks with fewer user transactions",
    )
    ap.add_argument("--network", default="MONAD_TEN")
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--rpc", action="append", help="RPC URL (repeatable)")
    args = ap.parse_args()

    rpc = Rpc(args.rpc or DEFAULT_RPCS)
    os.makedirs(args.out, exist_ok=True)
    blocks = args.blocks or sample_blocks(
        rpc, args.count, args.span, args.seed, args.min_txs
    )

    def work(n):
        path = os.path.join(args.out, f"monad_mainnet_{n}.json")
        if os.path.exists(path):
            return n, "cached"
        fixture = build_fixture(Rpc(args.rpc or DEFAULT_RPCS), n, args.network)
        tmp = path + ".tmp"
        with open(tmp, "w") as f:
            json.dump(fixture, f)
        os.replace(tmp, path)
        return n, "ok"

    failed = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        futs = {ex.submit(work, n): n for n in blocks}
        for i, fut in enumerate(concurrent.futures.as_completed(futs), 1):
            n = futs[fut]
            try:
                fut.result()
            except Exception as e:
                failed.append(n)
                print(f"block {n}: {e}", file=sys.stderr)
            if i % 25 == 0:
                print(f"{i}/{len(blocks)}", file=sys.stderr)
    print(f"{len(blocks) - len(failed)} fixtures in {args.out}, {len(failed)} failed")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
