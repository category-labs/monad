set(osaka_excluded_tests
    # Features modified by Osaka EIPs that we haven't yet implemented support for
    "BlockchainTests.frontier/precompiles/precompiles/precompiles.json"
    "BlockchainTests.byzantium/eip198_modexp_precompile/*"
    "BlockchainTests.cancun/eip4844_blobs/*"
    "BlockchainTests.prague/eip7702_set_code_tx/*"

    # New features in Osaka
    "BlockchainTests.osaka/eip7594_peerdas/*"
    "BlockchainTests.osaka/eip7918_blob_reserve_price/*"
    "BlockchainTests.osaka/eip7823_modexp_upper_bounds/*"
    "BlockchainTests.osaka/eip7934_block_rlp_limit/*"
    "BlockchainTests.osaka/eip7825_transaction_gas_limit_cap/*"
    "BlockchainTests.osaka/eip7883_modexp_gas_increase/*"
)