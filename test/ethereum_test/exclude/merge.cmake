set(merge_excluded_tests
    "BlockchainTests.GeneralStateTests/stCreate2/RevertInCreateInInitCreate2.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stCreate2/create2collisionStorage.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stRevertTest/RevertInCreateInInit.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stSStoreTest/InitCollision.json" # Incarnation
    "BlockchainTests.InvalidBlocks/bcEIP1559/badBlocks.json" # BaseFee
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
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheck.json" # Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate.json" # Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate2.json" #I ncarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideThenCheckBalance.json" # Incarnation
    "TransactionTests.ttEIP1559/GasLimitPriceProductOverflowtMinusOne.json"
    "TransactionTests.ttEIP2930/accessListStorage32Bytes.json"
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding01.json"
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding127.json"
)
