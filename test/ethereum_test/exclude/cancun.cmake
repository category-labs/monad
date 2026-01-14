set(cancun_excluded_tests
    # Blobs (EIP-4844)
    "BlockchainTests.GeneralStateTests/Pyspecs/cancun/eip4844_blobs/*"
    "BlockchainTests.cancun/eip4844_blobs/*"

    # withdrawals root
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/incorrectWithdrawalsRoot.json"

    # EIP-1559
    "BlockchainTests.InvalidBlocks/bcEIP1559/badBlocks.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/badUncles.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/baseFee.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/checkGasLimit.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/feeCap.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit20m.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit40m.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/intrinsicOrFail.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/transFail.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/valCausesOOF.json"

    # Stricter validation
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/accountInteractions.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/badBlocks.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/badUncles.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/baseFee.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/checkGasLimit.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/feeCap.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit20m.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit40m.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/intrinsicOrFail.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/transFail.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/valCausesOOF.json"
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
    "BlockchainTests.InvalidBlocks/bcStateTests/CreateTransactionReverted.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/RefundOverflow.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/RefundOverflow2.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/callcodeOutput2.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/createNameRegistratorPerTxsNotEnoughGasAt.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/dataTx.json"

    # Slow + stack-heavy tests
    "BlockchainTests.GeneralStateTests/stBadOpcode/*"
    "BlockchainTests.GeneralStateTests/stBugs/*"
    "BlockchainTests.GeneralStateTests/stCallCodes/*"
    "BlockchainTests.GeneralStateTests/stCallCreateCallCodeTest/*"
    "BlockchainTests.GeneralStateTests/stCallDelegateCodesCallCodeHomestead/*"
    "BlockchainTests.GeneralStateTests/stCallDelegateCodesHomestead/*"
    "BlockchainTests.GeneralStateTests/stCreate2/*"
    "BlockchainTests.GeneralStateTests/stCreateTest/*"

    # Stricter validation of base fee
    "BlockchainTests.london/validation/test_invalid_header.json"

    # EIP-7610
    "BlockchainTests.GeneralStateTests/stCreate2/RevertInCreateInInitCreate2Paris.json"
    "BlockchainTests.GeneralStateTests/stCreate2/create2collisionStorageParis.json"
    "BlockchainTests.GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json"
    "BlockchainTests.GeneralStateTests/stRevertTest/RevertInCreateInInit_Paris.json"
    "BlockchainTests.GeneralStateTests/stSStoreTest/InitCollisionParis.json"
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_opcode.json"
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_tx.json"
    "BlockchainTests.static/state_tests/stCreate2/RevertInCreateInInitCreate2Paris.json"
    "BlockchainTests.static/state_tests/stCreate2/create2collisionStorageParis.json"
    "BlockchainTests.static/state_tests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json"
)