Feature: Configure Logger

    Background: BlockDb path setup
        Given I run with BlockDb path = "erigon/block_db"
        And I run with start block number = "46147"
        And I run with finish block number = "46148"

    Scenario: Using default log level
        Given I run with default log level
        When I start "replay_ethereum"
        Then the output should contain "txn_logger" "Info" log
        And the output should contain "trie_db_logger" "Info" log
        But the output should not contain "block_logger" "Debug" log 

    Scenario: Setting block_logger log_level = Debug
        Given I run with "block_logger" log level = "Debug"
        When I start "replay_ethereum"
        Then the output should contain "block_logger" "Debug" log 
        And the output should contain "txn_logger" "Info" log
        And the output should contain "trie_db_logger" "Info" log

    Scenario: Setting txn_logger log_level = Warning
        Given I run with "txn_logger" log level = "Warning"
        When I start "replay_ethereum"
        Then the output should contain "trie_db_logger" "Info" log
        But the output should not contain "txn_logger" "Info" log 
        But the output should not contain "block_logger" "Debug" log 

    Scenario: Turn off all logging
        Given I run with "main_logger" log level = "Warning"
        And I run with "txn_logger" log level = "Warning"
        And I run with "block_logger" log level = "Warning"
        And I run with "trie_db_logger" log level = "Warning"
        When I start "replay_ethereum"
        Then the output should be empty
