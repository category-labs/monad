from trie import HexaryTrie  # type: ignore
import argparse
import os
import pickle
import re
from binascii import unhexlify, hexlify
from enum import Enum
from typing import List, Optional


class Upsert:
    def __init__(self, key: bytes, value: bytes):
        self.key = key
        self.value = value


class Delete:
    def __init__(self, key: bytes):
        self.key = key


def parse_update(update: str) -> Upsert | Delete:
    assert len(update) == 2

    if update[0] == "UPSERT":
        kv = re.findall(r"(?:key=0x)(.*?) (?:value=0x)(.*?)}", update[1])
        assert len(kv) == 1
        assert len(kv[0]) == 2
        return Upsert(unhexlify(kv[0][0]), unhexlify(kv[0][1]))
    elif update[0] == "DELETE":
        kv = re.findall(r"(?:key=0x)(.*?)}", update[1])
        assert len(kv) == 1
        return Delete(unhexlify(kv[0]))
    else:
        assert False


def parse_updates(line: str) -> List[Upsert | Delete]:
    ret: List[Upsert | Delete] = []
    updates = re.findall(r"(UPSERT|DELETE)(\{(?:.*?)})", line)

    for update in updates:
        ret += [parse_update(update)]

    assert len(ret) > 0

    return ret


class TrieType(Enum):
    ACCOUNT = 1
    STORAGE = 2


def parse_header(line: str) -> Optional[TrieType]:
    header = re.findall(r"trie_db_logger (STORAGE_UPDATES|ACCOUNT_UPDATES)", line)
    if len(header) == 0:
        return None
    assert len(header) == 1

    if header[0] == "STORAGE_UPDATES":
        return TrieType.STORAGE
    elif header[0] == "ACCOUNT_UPDATES":
        return TrieType.ACCOUNT
    else:
        assert False


def parse_account(line: str) -> bytes:
    account = re.findall(r"STORAGE_UPDATES\(\d*\) account=0x(.*?) ", line)
    assert len(account) == 1
    return unhexlify(account[0])


def main(parse_args: Optional[List[str]] = None):
    parser = argparse.ArgumentParser(prog="tdb", description="Trie Debugger")
    parser.add_argument(
        "--log", required=True, help="path to log file to process", type=os.path.abspath  # type: ignore
    )

    def account_type(account: str):
        if not re.match(r"^0x[a-f|\d]{40}$", account):
            raise argparse.ArgumentTypeError("Invalid account format")
        return unhexlify(account[2:])

    parser.add_argument(
        "--account",
        required=False,
        help="optional argument to process only a specific storage trie",
        type=account_type,
    )

    parser.add_argument(
        "--save",
        required=False,
        help="optional argument to save the trie database after processing",
        type=os.path.abspath,  # type: ignore
    )

    args = parser.parse_args(parse_args)

    trie = HexaryTrie(db={})

    with open(args.log, "r") as f:
        for line in f:
            type = parse_header(line)

            if type is None:
                continue

            if args.account:
                if type != TrieType.STORAGE or parse_account(line) != args.account:
                    continue
            elif type == TrieType.STORAGE:
                continue

            updates = parse_updates(line)

            for update in updates:
                if isinstance(update, Upsert):
                    trie.set(update.key, update.value)
                else:
                    trie.delete(update.key)

    if args.save:
        with open(  # type: ignore
            args.save,
            "wb",
        ) as f:
            pickle.dump(trie.db, f)  # type: ignore

    return trie.root_hash


if __name__ == "__main__":
    root_hash = main()
    print(f"Root hash 0x{hexlify(root_hash).decode()}")
