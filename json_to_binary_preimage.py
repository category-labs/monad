import json
from eth_hash.auto import keccak
import time
import sys
import os

input_json = sys.argv[1]
fin = open(input_json, "r")
output_dir = os.path.dirname(input_json)
faccounts = open(os.path.join(output_dir, "accounts"), "wb", buffering=4096)
fcode = open(os.path.join(output_dir,"code"), "wb", buffering=4096)
code_dict = {}

j = json.load(fin)
print("Done loading")
for k, v in j.items():
    assert(len(k) == 42) # 0x + 40 hex chars
    key = bytes.fromhex(k[2:])
    balance = int(v["balance"]).to_bytes(32, 'little')
    nonce = int(v["nonce"], 16).to_bytes(8, 'little')
    code = bytes.fromhex(v["code"][2:])
    code_hash = keccak(code)
    code_dict[code_hash] = code
    num_storage = len(v["storage"]).to_bytes(8, 'little')

    assert len(key) == 20 # address 
    assert len(balance) == 32
    assert len(nonce) == 8
    assert len(code_hash) == 32
    assert len(num_storage) == 8

    faccounts.write(key)
    faccounts.write(balance)
    faccounts.write(nonce)
    faccounts.write(code_hash)
    faccounts.write(num_storage)

    for sk, sv in v["storage"].items():
        skey = bytes.fromhex(sk[2:])
        sval = bytes.fromhex(sv['value'][2:])
        assert len(skey) == 32
        assert len(sval) == 32
        faccounts.write(skey)
        faccounts.write(sval)

for k, v in code_dict.items():
    code_len = len(v).to_bytes(8, 'little')

    assert len(k) == 32
    assert len(code_len) == 8

    fcode.write(k)
    fcode.write(code_len)
    fcode.write(v)
    
   