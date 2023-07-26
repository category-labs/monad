Feature: Run Ethereum Block History

    Background: BlockDb path setup
        Given I run with BlockDb path = "erigon/block_db"

    Scenario: Run ethereum block history for all initial blocks with no transaction
        Given I run with start block number = "0"
        And I run with finish block number = "46147"
        And I run with "trie_db_logger" log level = "Critical"
        When I start "replay_ethereum"
        Then the "State Root" should match
        And the "Receipt Root" should match
        And the "Transaction Root" should match