set(shanghai_excluded_tests
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/incorrectWithdrawalsRoot.json" # Trie
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsAddressBounds.json" # RLP
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsRLPmoreElements.json" # RLP
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsRLPlessElements.json" # RLP
    "BlockchainTests.GeneralStateTests/stCreate2/RevertInCreateInInitCreate2.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stCreate2/create2collisionStorage.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stRevertTest/RevertInCreateInInit.json" # Incarnation
    "BlockchainTests.GeneralStateTests/stSStoreTest/InitCollision.json" # Incarnation
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
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheck.json" # Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate.json" # Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate2.json" # Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideThenCheckBalance.json" # Incarnation
    "TransactionTests.ttAddress/AddressLessThan20.json"
    "TransactionTests.ttAddress/AddressMoreThan20.json"
    "TransactionTests.ttAddress/AddressMoreThan20PrefixedBy0.json"
    "TransactionTests.ttEIP1559/GasLimitPriceProductOverflow.json"
    "TransactionTests.ttEIP1559/GasLimitPriceProductOverflowtMinusOne.json"
    "TransactionTests.ttEIP1559/GasLimitPriceProductPlusOneOverflow.json"
    "TransactionTests.ttEIP1559/maxFeePerGas00prefix.json"
    "TransactionTests.ttEIP1559/maxFeePerGas32BytesValue.json"
    "TransactionTests.ttEIP1559/maxFeePerGasOverflow.json"
    "TransactionTests.ttEIP1559/maxPriorityFeePerGas00prefix.json"
    "TransactionTests.ttEIP1559/maxPriorityFeePerGasOverflow.json"
    "TransactionTests.ttEIP1559/maxPriorityFeePerGass32BytesValue.json"
    "TransactionTests.ttEIP2930/accessListAddressGreaterThan20.json"
    "TransactionTests.ttEIP2930/accessListAddressLessThan20.json"
    "TransactionTests.ttEIP2930/accessListAddressPrefix00.json"
    "TransactionTests.ttEIP2930/accessListStorage0x0001.json"
    "TransactionTests.ttEIP2930/accessListStorage32Bytes.json"
    "TransactionTests.ttEIP2930/accessListStorageOver32Bytes.json"
    "TransactionTests.ttEIP2930/accessListStoragePrefix00.json"
    "TransactionTests.ttGasPrice/TransactionWithLeadingZerosGasPrice.json"
    "TransactionTests.ttNonce/TransactionWithLeadingZerosNonce.json"
    "TransactionTests.ttNonce/TransactionWithZerosBigInt.json"
    "TransactionTests.ttRSValue/TransactionWithRvaluePrefixed00BigInt.json"
    "TransactionTests.ttRSValue/TransactionWithSvalueHigh.json"
    "TransactionTests.ttRSValue/TransactionWithSvalueLargerThan_c_secp256k1n_x05.json"
    "TransactionTests.ttRSValue/TransactionWithSvaluePrefixed00BigInt.json"
    "TransactionTests.ttSignature/TransactionWithTooManyRLPElements.json"
    "TransactionTests.ttVValue/ValidChainID1InvalidV00.json"
    "TransactionTests.ttVValue/ValidChainID1InvalidV01.json"
    "TransactionTests.ttValue/TransactionWithLeadingZerosValue.json"
    "TransactionTests.ttWrongRLP/RLPAddressWithFirstZeros.json"
    "TransactionTests.ttWrongRLP/RLPAddressWrongSize.json"
    "TransactionTests.ttWrongRLP/RLPArrayLengthWithFirstZeros.json"
    "TransactionTests.ttWrongRLP/RLPExtraRandomByteAtTheEnd.json"
    "TransactionTests.ttWrongRLP/RLPHeaderSizeOverflowInt32.json"
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding00.json"
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding01.json"
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding127.json"
    "TransactionTests.ttWrongRLP/RLPListLengthWithFirstZeros.json"
    "TransactionTests.ttWrongRLP/RLPTransactionGivenAsArray.json"
    "TransactionTests.ttWrongRLP/RLP_04_maxFeePerGas32BytesValue.json"
    "TransactionTests.ttWrongRLP/RLP_09_maxFeePerGas32BytesValue.json"
    "TransactionTests.ttWrongRLP/TRANSCT_HeaderGivenAsArray_0.json"
    "TransactionTests.ttWrongRLP/TRANSCT_HeaderLargerThanRLP_0.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_0.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_1.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_2.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_3.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_5.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_6.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_7.json"
    "TransactionTests.ttWrongRLP/TRANSCT__RandomByteAtRLP_8.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_0.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_1.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_2.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_3.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_4.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_5.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_6.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_7.json"
    "TransactionTests.ttWrongRLP/TRANSCT__ZeroByteAtRLP_8.json"
    "TransactionTests.ttWrongRLP/TRANSCT_to_Prefixed0000.json"
    "TransactionTests.ttWrongRLP/TRANSCT_to_TooLarge.json"
    "TransactionTests.ttWrongRLP/TRANSCT_to_TooShort.json"
    "TransactionTests.ttWrongRLP/aCrashingRLP.json"
    "TransactionTests.ttWrongRLP/aMaliciousRLP.json"
)
