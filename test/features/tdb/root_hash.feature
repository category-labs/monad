Feature: TDB Root Hash

    # TODO: make this generate the data from replay_ethereum when that becomes ready
    Scenario: Verify state root hash from TrieDBTest/1.ModifyStorageOfAccount
        Given I run db unit test TrieDBTest/1.ModifyStorageOfAccount
        And I run tdb with the output
        Then the output should contain "Root hash 0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60"  

    Scenario: Verify storage root hash from TrieDBTest/1.ModifyStorageOfAccount
        Given I run db unit test TrieDBTest/1.ModifyStorageOfAccount
        And I run tdb with the output and account 0x5353535353535353535353535353535353535353 
        Then the output should contain "Root hash 0xf0481d515d9698359549c6d184c2fd05e17a35a0a2cb4726c5442e715158b9bd"  
