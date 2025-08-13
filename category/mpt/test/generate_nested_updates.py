# Copyright (C) 2025 Category Labs, Inc.
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
