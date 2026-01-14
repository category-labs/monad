set(prague_excluded_tests
    # Blobs (EIP-4844)
    "BlockchainTests.cancun/eip4844_blobs/*"

    # Unimplemented Prague EIPs
    "BlockchainTests.prague/eip6110_deposits/*"
    "BlockchainTests.prague/eip7002_el_triggerable_withdrawals/*"
    "BlockchainTests.prague/eip7251_consolidations/*"
    "BlockchainTests.prague/eip7685_general_purpose_el_requests/*"

    # Long-running tests
    "BlockchainTests.prague/eip2935_historical_block_hashes_from_state/block_hashes/block_hashes_history.json"

    # Stricter validation of base fee
    "BlockchainTests.london/validation/test_invalid_header.json"

    # EIP-7610
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_opcode.json"
    "BlockchainTests.paris/eip7610_create_collision/test_init_collision_create_tx.json"
    "BlockchainTests.static/state_tests/stCreate2/RevertInCreateInInitCreate2Paris.json"
    "BlockchainTests.static/state_tests/stCreate2/create2collisionStorageParis.json"
    "BlockchainTests.static/state_tests/stExtCodeHash/dynamicAccountOverwriteEmpty_Paris.json"
)
