set(prague_excluded_tests
    # Blobs (EIP-4844)
    "BlockchainTests.frontier/scenarios/scenarios/scenarios.json"
    "BlockchainTests.cancun/eip4844_blobs/*"
    "BlockchainTests.cancun/eip4788_beacon_root/beacon_root_contract/tx_to_beacon_root_contract.json"

    # Unimplemented Prague EIPs
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
    "BlockchainTests.osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/transaction_gas_limit_cap.json"

    # Long-running tests
    "BlockchainTests.prague/eip2935_historical_block_hashes_from_state/block_hashes/block_hashes_history.json"
)