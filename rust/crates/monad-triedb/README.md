# monad-triedb

Triedb stores the blockchain state (i.e. account balance, contract bytecode, value at a particular storage slot etc), code, and block data. The schema are documented as follows.

## State 
**Account**
```
key: <state nibble (0): 1 nibble><keccak256(address): 32 bytes>
value: rlp([nonce, balance, code_hash])
```

**Storage**
```
key: <state nibble (0): 1 nibble><keccak256(address): 32 bytes><keccak256(key): 32 bytes>
value: rlp(zeroless_view(storage_data)) | rlp(zeroless_view(storage_slot))
```

## Code
```
key: <code nibble (1): 1 nibble><code hash: 32 bytes>
value: code
```

## Receipt
```
key: <receipt nibble (2): 1 nibble><rlp(transaction index)>
value: rlp([rlp_encode_string(encoded_receipt), rlp(log_index_start)])
```

## Block Data

Each db version has block data corresponding to that block number

**Block header**
```
key: <block header nibble (4): 1 nibble>
value: rlp(block_header)
```

**Transaction**
```
key: <transaction nibble (3): 1 nibble><rlp(transaction index)>
value: rlp([rlp_encode_string(encoded_transaction), rlp(sender_addr)])
```

**Withdrawal**
```
key: <withdrawal nibble (5): 1 nibble><rlp(withdrawal index)>
value: rlp(withdrawal)
```

**Ommers**
```
key: <ommers nibble (6): 1 nibble>
value: rlp(ommers_list)
```

## Tx Hash
```
key: <tx hash nibble (7): 1 nibble><keccak(rlp(tx))>
value: rlp([block_number, transaction_index])
```

## Block Hash
```
key: <block hash nibble (8): 1 nibble><keccak(rlp(block_header))>
value: rlp(block_number)
```

## Call Frames
```
key: <block hash nibble (9): 1 nibble><4 bytes tx index, 1 byte chunk index>
value: rlp(call_frames)
```