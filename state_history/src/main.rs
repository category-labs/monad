use cxx::let_cxx_string;

// Example of how to use state_history
fn main() {
    let_cxx_string!(root = "/path/to/database/root");
    let client = state_history::ffi::make_client(&root);
    assert!(client.is_ok());
    let account = client
        .unwrap()
        .get_account([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    assert!(account.is_ok());
    assert!(account.unwrap().get_nonce() == 0);
}
