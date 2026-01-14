set(shanghai_excluded_tests
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/incorrectWithdrawalsRoot.json" # Trie
    "BlockchainTests.InvalidBlocks/bcEIP1559/badBlocks.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcEIP1559/badUncles.json" # Mixed
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit20m.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit40m.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcEIP3675/timestampPerBlock.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/badTimestamp.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/timeDiff0.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongCoinbase.json" # StateRoot
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongGasLimit.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash2.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongReceiptTrie.json" # Trie
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongStateRoot.json" # StateRoot
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTimestamp.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTransactionsTrie.json" # Trie
    "BlockchainTests.InvalidBlocks/bcMultiChainTest/UncleFromSideChain.json" # Uncle
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding01.json"
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding127.json"

    # Stricter validation of base fee
    "BlockchainTests.london/validation/test_invalid_header.json"

    # EIP-7610
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_opcode.json"
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_tx.json"
)
