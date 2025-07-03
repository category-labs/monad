set(cancun_excluded_tests
    # Proto danksharking (unimplemented)
    "BlockchainTests.GeneralStateTests/Cancun/stEIP4844_blobtransactions/*"
    "BlockchainTests.GeneralStateTests/Pyspecs/cancun/eip4844_blobs/*"
    "BlockchainTests.cancun/eip4844_blobs/*"
    # new precompile (unimplemented)
    "BlockchainTests.GeneralStateTests/Pyspecs/shanghai/eip4895_withdrawals/withdrawing_to_precompiles.json"
    "BlockchainTests.shanghai/eip4895_withdrawals/withdrawals/withdrawing_to_precompiles.json"
    # test includes new tx type (unimplemented)
    "BlockchainTests.GeneralStateTests/Pyspecs/cancun/eip4788_beacon_root/tx_to_beacon_root_contract.json"
    "BlockchainTests.cancun/eip4788_beacon_root/beacon_root_contract/tx_to_beacon_root_contract.json"
    # MCOPY (unimplemented)
    "BlockchainTests.GeneralStateTests/Cancun/stEIP5656-MCOPY/*"
    "BlockchainTests.InvalidBlocks/bc4895_withdrawals/incorrectWithdrawalsRoot.json"
    "BlockchainTests.GeneralStateTests/stBadOpcode/*"
    "BlockchainTests.GeneralStateTests/stBugs/*"
    "BlockchainTests.GeneralStateTests/stCallCodes/*"
    "BlockchainTests.GeneralStateTests/stCallCreateCallCodeTest/*"
    "BlockchainTests.GeneralStateTests/stCallDelegateCodesCallCodeHomestead/*"
    "BlockchainTests.GeneralStateTests/stCallDelegateCodesHomestead/*"
    "BlockchainTests.GeneralStateTests/stCreate2/*"
    "BlockchainTests.GeneralStateTests/stCreateTest/*"
    # Stricter validation
    "BlockchainTests.InvalidBlocks/bcEIP1559/badBlocks.json" # BaseFee
    "BlockchainTests.InvalidBlocks/bcEIP1559/badUncles.json" # Mixed
    "BlockchainTests.InvalidBlocks/bcEIP1559/baseFee.json" # BaseFee
    "BlockchainTests.InvalidBlocks/bcEIP1559/checkGasLimit.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/feeCap.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit20m.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcEIP1559/gasLimit40m.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcEIP1559/intrinsicOrFail.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/transFail.json"
    "BlockchainTests.InvalidBlocks/bcEIP1559/valCausesOOF.json"
    "BlockchainTests.InvalidBlocks/bcEIP3675/timestampPerBlock.json"
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/badTimestamp.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcInvalidHeaderTest/wrongGasLimit.json" # ParentHeader
    "BlockchainTests.InvalidBlocks/bcMultiChainTest/UncleFromSideChain.json" # Uncle
    "BlockchainTests.InvalidBlocks/bcStateTests/CreateTransactionReverted.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/RefundOverflow.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/RefundOverflow2.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/callcodeOutput2.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/createNameRegistratorPerTxsNotEnoughGasAt.json"
    "BlockchainTests.InvalidBlocks/bcStateTests/dataTx.json"
    "BlockchainTests.ValidBlocks/bcEIP4844_blobtransactions/blockWithAllTransactionTypes.json"
    "BlockchainTests.ValidBlocks/bcValidBlockTest/reentrencySuicide.json"
    # misc
    "BlockchainTests.GeneralStateTests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json"
    "BlockchainTests.GeneralStateTests/stPreCompiledContracts/idPrecomps.json"
    "BlockchainTests.GeneralStateTests/stPreCompiledContracts/precompsEIP2929Cancun.json"
    "BlockchainTests.GeneralStateTests/stRevertTest/RevertInCreateInInit_Paris.json"
    "BlockchainTests.GeneralStateTests/stSpecialTest/failed_tx_xcf416c53_Paris.json"
    "BlockchainTests.GeneralStateTests/stSStoreTest/InitCollisionParis.json"
    "BlockchainTests.frontier/precompiles/precompiles/precompiles.json"
    "BlockchainTests.frontier/scenarios/scenarios/scenarios.json")
