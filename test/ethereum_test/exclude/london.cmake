set(london_excluded_tests
    "BlockchainTests.InvalidBlocks/bcEIP1559/badBlocks.json" # BaseFee
    "BlockchainTests.InvalidBlocks/bcEIP1559/badUncles.json" # Mixed
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit20m.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit40m.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/DifficultyIsZero.json" # Difficulty (Pre-merge)
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/badTimestamp.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/timeDiff0.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongCoinbase.json" # StateRoot
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongDifficulty.json" # Difficulty (Pre-merge)
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongGasLimit.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongParentHash2.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongReceiptTrie.json" # Trie
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongStateRoot.json"  # StateRoot
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTimestamp.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongTransactionsTrie.json" # Trie
    "BlockchainTests.InvalidBlocks/bcMultiChainTest/UncleFromSideChain.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/diffTooHigh.json" # Difficulty (Pre-merge)
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/diffTooLow.json" # Difficulty (Pre-merge)
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/diffTooLow2.json" # Difficulty (Pre-merge)
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooHigh.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooHighExactBound.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLow.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLowExactBound.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLowExactBound2.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/gasLimitTooLowExactBoundLondon.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleNumber0.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleNumber1.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleNumber500.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleTimestamp.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleTimestamp2.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/incorrectUncleTimestamp3.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/pastUncleTimestamp.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/unknownUncleParentHash.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleHeaderValidity/wrongParentHash.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcUncleTest/EqualUncleInTwoDifferentBlocks.json"  # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncle.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleFather.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGrandPa.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGrandPa.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGreatGrandPa.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGreatGreatGrandPa.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/InChainUncleGreatGreatGreatGreatGrandPa.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/UncleIsBrother.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/oneUncleGeneration7.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/uncleHeaderWithGeneration0.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcUncleTest/uncleWithSameBlockNumber.json" # Uncle
    "BlockchainTests.ValidBlocks/bcGasPricerTest/RPC_API_Test.json" # Multichain
    "BlockchainTests.ValidBlocks/bcMultiChainTest/CallContractFromNotBestBlock.json" # Multichain
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainB.json" # Multichain
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainBCallContractFormA.json" # Multichain
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainB_BlockHash.json" # Multichain
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainB_difficultyB.json" # Multichain
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainBtoChainA.json" # Multichain
    "BlockchainTests.ValidBlocks/bcMultiChainTest/ChainAtoChainBtoChainAtoChainB.json" # Multichain
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/lotsOfBranchesOverrideAtTheEnd.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/lotsOfBranchesOverrideAtTheMiddle.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/lotsOfLeafs.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/newChainFrom4Block.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/newChainFrom5Block.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/newChainFrom6Block.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/sideChainWithMoreTransactions.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/sideChainWithMoreTransactions2.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/sideChainWithNewMaxDifficultyStartingFromBlock3AfterBlock4.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/uncleBlockAtBlock3AfterBlock3.json" # Difficulty (Pre-merge)
    "BlockchainTests.ValidBlocks/bcTotalDifficultyTest/uncleBlockAtBlock3afterBlock4.json" # Difficulty (Pre-merge)
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding01.json"
    "TransactionTests.ttWrongRLP/RLPIncorrectByteEncoding127.json"

    # Stricter validation of base fee
    "BlockchainTests.london/validation/test_invalid_header.json"
)
