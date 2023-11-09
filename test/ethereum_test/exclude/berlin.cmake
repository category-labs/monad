set(berlin_excluded_tests
    "BlockchainTests.GeneralStateTests/stTransactionTest/ValueOverflow.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcBlockRLPAsList.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcBlockRLPPrefixed0000.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcBlockRLPRandomByte.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcBlockRLPTooLarge.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcBlockRLPZeroByte.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcForkBlockTest.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcInvalidRLPTest_BLOCK.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcInvalidRLPTest_TRANSACT.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcTransactRLPRandomByte.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcTransactRLPTooLarge.json" #RLP
    "BlockchainTests.InvalidBlocks/bcForgedTest/bcTransactRLPZeroByte.json" #RLP
    "GeneralStateTests.stCreate2/RevertInCreateInInitCreate2.json" #Incarnation
    "GeneralStateTests.stCreate2/create2collisionStorage.json" #Incarnation
    "GeneralStateTests.stExtCodeHash/dynamicAccountOverwriteEmpty.json" #Incarnation
    "GeneralStateTests.stRevertTest/RevertInCreateInInit.json" #Incarnation
    "GeneralStateTests.stSStoreTest/InitCollision.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stCreate2/RevertInCreateInInitCreate2.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stCreate2/create2collisionStorage.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty.json" #Incarnation
    "BlockchainTests.GeneralStateTests/stRevertTest/RevertInCreateInInit.json" #Incarantion
    "BlockchainTests.GeneralStateTests/stSStoreTest/InitCollision.json" #Incarnation
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/DifficultyIsZero.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/timeDiff0.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongCoinbase.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongDifficulty.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongGasLimit.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash2.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongReceiptTrie.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongStateRoot.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTimestamp.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTransactionsTrie.json"
    "BlockchainTests.InvalidBlocks/bcMultiChainTest/UncleFromSideChain.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/diffTooHigh.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/diffTooLow.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/diffTooLow2.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooHigh.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooHighExactBound.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLow.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLowExactBound.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLowExactBound2.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLowExactBoundLondon.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleNumber0.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleNumber1.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleNumber500.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleTimestamp.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleTimestamp2.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleTimestamp3.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/pastUncleTimestamp.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/unknownUncleParentHash.json"
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/wrongParentHash.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/EqualUncleInTwoDifferentBlocks.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncle.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleFather.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGrandPa.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGrandPa.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGreatGrandPa.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGreatGreatGrandPa.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGreatGreatGreatGrandPa.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/UncleIsBrother.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/oneUncleGeneration7.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/uncleHeaderWithGeneration0.json"
    "BlockchainTests.InvalidBlocks/bcUncleTest/uncleWithSameBlockNumber.json"
    "BlockchainTests.ValidBlocks/bcForkStressTest/ForkStressTest.json"
    "BlockchainTests.ValidBlocks/bcGasPricerTest/RPC_API_Test.json"
    "BlockchainTests.ValidBlocks/bcMultiChainTest/CallContractFromNotBestBlock.json"
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainB.json"
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainBCallContractFormA.json"
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainB_BlockHash.json"
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainB_difficultyB.json"
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainBtoChainA.json"
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainBtoChainAtoChainB.json"
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheck.json" #Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate.json" #Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideStorageCheckVCreate2.json" #Incarnation
    "BlockchainTests.ValidBlocks/bcStateTests/suicideThenCheckBalance.json" #Incarnation
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/lotsOfBranchesOverrideAtTheEnd.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/lotsOfBranchesOverrideAtTheMiddle.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/lotsOfLeafs.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/newChainFrom4Block.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/newChainFrom5Block.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/newChainFrom6Block.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/sideChainWithMoreTransactions.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/sideChainWithMoreTransactions2.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/sideChainWithNewMaxDifficultyStartingFromBlock3AfterBlock4.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/uncleBlockAtBlock3AfterBlock3.json"
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/uncleBlockAtBlock3afterBlock4.json"
)