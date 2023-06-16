Feature: Configure Logger

    Scenario: Using default log level
        Given I run with BlockDb path = "erigon/block_db"
        And I run with start block number = "3000000"
        And I run with finish block number = "3000001"
        And I run with default log level
        When I start "replay_ethereum"
        Then the output should not contain "BlockHeader Fields:"
        And the output should not contain "Log"
        And the output should contain "Start executing Transaction"

    Scenario: Setting block_logger log_level = Debug
        Given I run with BlockDb path = "erigon/block_db"
        And I run with start block number = "3000000"
        And I run with finish block number = "3000001"
        And I run with "block_logger" log level = "Debug"
        When I start "replay_ethereum"
        Then the output should contain "BlockHeader Fields"
        And the output should contain "Log"
        And the output should contain "Start executing Transaction"

    Scenario: Setting txn_logger log_level = Warning
        Given I run with BlockDb path = "erigon/block_db"
        And I run with start block number = "3000000"
        And I run with finish block number = "3000001"
        And I run with "txn_logger" log level = "Warning"
        When I start "replay_ethereum"
        Then the output should not contain "BlockHeader Fields:"
        And the output should not contain "Log"
        And the output should not contain "Start executing Transaction"

    Scenario: Turn off all logging
        Given I run with BlockDb path = "erigon/block_db"
        And I run with start block number = "3000000"
        And I run with finish block number = "3000001"
        And I run with "main_logger" log level = "Warning"
        And I run with "txn_logger" log level = "Warning"
        And I run with "block_logger" log level = "Warning"
        When I start "replay_ethereum"
        Then the output should be empty
