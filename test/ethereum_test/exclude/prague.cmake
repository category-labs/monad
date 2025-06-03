set(prague_excluded_tests
    # Despite being for previous revisions, these tests are from the execution
    # spec tests corpus and therefore include cases filled using Prague network
    # parameters. We can't run them until enough Prague support is implemented.
    "BlockchainTests.berlin/*"
    "BlockchainTests.byzantium/*"
    "BlockchainTests.cancun/*"
    "BlockchainTests.constantinople/*"
    "BlockchainTests.frontier/*"
    "BlockchainTests.homestead/*"
    "BlockchainTests.istanbul/*"
    "BlockchainTests.paris/*"
    "BlockchainTests.shanghai/*"
    "BlockchainTests.zkevm/*"
    
    # Unimplemented Prague features
    "BlockchainTests.prague/eip7702_set_code_tx/*"
    "BlockchainTests.prague/eip2537_bls_12_381_precompiles/*"
    "BlockchainTests.prague/eip2935_historical_block_hashes_from_state/*"
    "BlockchainTests.prague/eip6110_deposits/*"
    "BlockchainTests.prague/eip7002_el_triggerable_withdrawals/*"
    "BlockchainTests.prague/eip7251_consolidations/*"
    "BlockchainTests.prague/eip7623_increase_calldata_cost/*"
    "BlockchainTests.prague/eip7685_general_purpose_el_requests/*"
)