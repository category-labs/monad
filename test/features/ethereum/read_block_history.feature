Feature: Read Ethereum Block History

  Scenario: Run replay_ethereum with invalid end block number
    Given I run with BlockDb path = "erigon/block_db"
    And I run with start block number = "1"
    And I run with finish block number = "1"
    When I start "replay_ethereum"
    Then the output should not contain "block_logger"

  Scenario: Run replay_ethereum with correct configuration, 1 Block, no hash validation
    Given I run with BlockDb path = "erigon/block_db"
    And I run with start block number = "1"
    And I run with finish block number = "2"
    When I start "replay_ethereum"
    Then the output should contain "1" "Computed Transaction Root"
    And the output should contain "1" "Expected Transaction Root"
    And the output should contain "1" "Computed Receipt Root"
    And the output should contain "1" "Expected Receipt Root"
    And the output should contain "1" "Computed State Root"
    And the output should contain "1" "Expected State Root"

  Scenario: Run replay_ethereum with correct configuration, 1000 Blocks, no hash validation
    Given I run with BlockDb path = "erigon/block_db"
    And I run with start block number = "10"
    And I run with finish block number = "1010"
    When I start "replay_ethereum"
    Then the output should contain "1000" "Computed Transaction Root"
    And the output should contain "1000" "Expected Transaction Root"
    And the output should contain "1000" "Computed Receipt Root"
    And the output should contain "1000" "Expected Receipt Root"
    And the output should contain "1000" "Computed State Root"
    And the output should contain "1000" "Expected State Root"

  Scenario: Run replay_ethereum with correct configuration, 1 Block, with hash validation
    Given I run with BlockDb path = "erigon/block_db"
    And I run with start block number = "1"
    And I run with finish block number = "2"
    When I start "replay_ethereum"
    Then the "Transaction Root" should match
    And the "Receipt Root" should match
    And the "State Root" should match