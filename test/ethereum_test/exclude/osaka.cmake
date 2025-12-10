set(osaka_excluded_tests
    # Features modified by Osaka EIPs that we haven't yet implemented support for
    "BlockchainTests.cancun/eip4844_blobs/*"

    # New features in Osaka
    "BlockchainTests.osaka/eip7594_peerdas/*"
    "BlockchainTests.osaka/eip7934_block_rlp_limit/*"
    "BlockchainTests.osaka/eip7825_transaction_gas_limit_cap/*"
)