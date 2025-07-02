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
    
    # Unimplemented Prague EIPs
    "BlockchainTests.prague/eip7702_set_code_tx/*"
    "BlockchainTests.prague/eip6110_deposits/*"
    "BlockchainTests.prague/eip7002_el_triggerable_withdrawals/*"
    "BlockchainTests.prague/eip7251_consolidations/*"
    "BlockchainTests.prague/eip7685_general_purpose_el_requests/*"

    # Unimplemented tx types
    "BlockchainTests.prague/eip7623_increase_calldata_cost/refunds/gas_refunds_from_data_floor.json"
    "BlockchainTests.prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_4.json"
    "BlockchainTests.prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_3.json"
    "BlockchainTests.prague/eip7623_increase_calldata_cost/execution_gas/gas_consumption_below_data_floor.json"
    "BlockchainTests.prague/eip7623_increase_calldata_cost/execution_gas/full_gas_consumption.json"

    # Long-running tests
    "BlockchainTests.prague/eip2935_historical_block_hashes_from_state/block_hashes/block_hashes_history.json"
)