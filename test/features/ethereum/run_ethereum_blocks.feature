Feature: Run Ethereum Block History

    Background: DB path setup
        Given I run with BlockDb path = "erigon/block_db"
        And I run with StateDb path = "RocksTrieDB"

    Scenario: Run ethereum block history for all initial blocks with no transaction
        Given I run with inferred start block number = "0"
        Given I run with finish block number = "46147"
        And I run with "trie_db_logger" log level = "Critical"
        When I start "replay_ethereum"
        Then the "State Root" should match
        And the "Receipt Root" should match
        And the "Transaction Root" should match