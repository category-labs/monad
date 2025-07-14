#!/usr/bin/python3
import sys, json
from random import Random
from trie import HexaryTrie

max_depth = 4
max_items = 10
seed = 0
if len(sys.argv) > 1:
   seed = str(sys.argv[1])
path = 'many_nested_updates.json'
if len(sys.argv) > 2:
   path = sys.argv[2]

rand = Random(seed)

def fill_level(depth: int) -> dict:
    ret = {}
    count = rand.randint(1, max_items)
    t = HexaryTrie(db={})
    for n in range(0, count):
        key = rand.randbytes(32)
        value = rand.randbytes(rand.randint(1, 60))
        if depth > 0:
            root_hash, contents = fill_level(depth - 1)
            # Vicky says random bits are appended by root hash for purposes of
            # total root hash calculation
            t[key] = value + root_hash
            value = { 'value' : value.hex(), 'subtrie' : contents }
        else:
            t[key] = value
            value = value.hex()
        ret[key.hex()] = value
    return (t.root_hash, ret)

root_hash, contents = fill_level(max_depth)
towrite = { 'updates' : contents, 'root_hash' : root_hash.hex()}
#print(towrite)
with open(path, 'w') as oh:
    json.dump(towrite, oh, indent = ' ')
