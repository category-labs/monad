#[cxx::bridge(namespace = "monad::state_history")]
pub mod ffi {
    unsafe extern "C++" {
        include!("state_history/include/client.hpp");

        type Account;

        fn get_balance(self: &Account) -> [u8; 32];
        fn get_nonce(self: &Account) -> u64;
        fn get_code_hash(self: &Account) -> [u8; 32];

        type Client;

        fn make_client(root: &CxxString) -> Result<UniquePtr<Client>>;
        fn make_client_at_block_number(
            root: &CxxString,
            block_number: u64,
        ) -> Result<UniquePtr<Client>>;

        fn get_account(self: &Client, address: [u8; 20]) -> Result<UniquePtr<Account>>;
        fn get_code(self: &Client, address: [u8; 20]) -> Result<&CxxString>;
        fn get_storage_hash(self: &Client, address: [u8; 20]) -> Result<[u8; 32]>;
        fn get_account_proof(self: &Client, address: [u8; 20]) -> Result<&CxxString>;
        fn get_storage_proof(self: &Client, address: [u8; 20], key: [u8; 32])
            -> Result<&CxxString>;
    }
}
