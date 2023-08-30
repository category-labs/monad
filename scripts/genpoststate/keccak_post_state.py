import json
import sys
import argparse

from Crypto.Hash import keccak


def keccak256_hash(hex_string):
    input_bytes = bytes.fromhex(hex_string[2:])
    return keccak.new(digest_bits=256, data=input_bytes).hexdigest()


def keccak_state(*, expected_state):
    new_state = {}
    for account in expected_state:
        keccaked_account = "0x" + keccak256_hash(account)
        new_state[keccaked_account] = expected_state[account]

        if "storage" in expected_state[account]:
            new_state[keccaked_account]["storage"] = {}
            for key, value in expected_state[account]["storage"].items():
                keccaked_key = "0x" + keccak256_hash(key)
                new_state[keccaked_account]["storage"][keccaked_key] = value
    return new_state


def main(expected_state):
    print(json.dumps(keccak_state(expected_state=expected_state)))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="A simple script to replace keccaked values in monad state with the original values."
    )

    args = parser.parse_args()

    input = "\n".join(list(map(lambda line: line.strip(), sys.stdin.readlines())))

    main(json.loads(input))
