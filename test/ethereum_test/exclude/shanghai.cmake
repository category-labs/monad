set(shanghai_excluded_tests
    "BlockchainTests.InvalidBlocks/bcEIP1559/badUncles.json"
    "BlockchainTests.GeneralStateTests/stTransactionTest/ValueOverflow.json" #RLP
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsAddressBounds.json"
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsAmountBounds.json"
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsIndexBounds.json"
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsRLPlessElements.json"
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsRLPnotAList.json"
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsValidatorIndexBounds.json"
    "GeneralStateTests.stCreate2/RevertInCreateInInitCreate2.json" #Incarnation
    "GeneralStateTests.stCreate2/create2collisionStorage.json" #Incarnation
    "GeneralStateTests.stExtCodeHash/dynamicAccountOverwriteEmpty.json" #Incarnation
    "GeneralStateTests.stRevertTest/RevertInCreateInInit.json" #Incarnation
    "GeneralStateTests.stSStoreTest/InitCollision.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stCreate2/RevertInCreateInInitCreate2.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stCreate2/create2collisionStorage.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stEIP1559/lowGasLimit.json"
    "BlockchainTests.GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stRevertTest/RevertInCreateInInit.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stSStoreTest/InitCollision.json" #Incarnation
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/incorrectWithdrawalsRoot.json"
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/withdrawalsRLPmoreElements.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/badBlocks.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit20m.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit40m.json"
    "BlockchainTests.InvalidBlocks/bcEIP3675/timestampPerBlock.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/badTimestamp.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/timeDiff0.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongCoinbase.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongGasLimit.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash2.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongReceiptTrie.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongStateRoot.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTimestamp.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTransactionsTrie.json"
    "BlockchainTests.InvalidBlocks/bcMultiChainTest/UncleFromSideChain.json"
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheck.json" #Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate.json" #Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate2.json" #Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideThenCheckBalance.json" #Incarnation
)