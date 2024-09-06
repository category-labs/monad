set(cancun_excluded_tests
    # All tests fail because EIP-4788 changes the state root, and all the tests
    # are interdependent.
    "BlockchainTests.*")
