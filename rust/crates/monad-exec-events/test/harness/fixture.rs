use std::collections::{BTreeMap, HashMap};

use alloy_primitives::{Address, Bytes, B256, U256, U64};
use serde::Deserialize;

pub type EthereumTestFixture = BTreeMap<String, EthereumTestCase>;

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EthereumTestCase {
    #[serde(rename = "_info")]
    pub info: EthereumTestInfo,
    pub env: EthereumTestEnvironment,
    pub pre: BTreeMap<Address, EthereumTestAccount>,
    pub transaction: EthereumTestTransaction,
    pub post: BTreeMap<EthereumTestFork, Vec<EthereumTestPostState>>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct EthereumTestInfo {
    pub comment: Option<String>,
    pub description: Option<String>,
    #[serde(rename = "filling-rpc-server")]
    pub filling_rpc_server: Option<String>,
    #[serde(rename = "filling-tool-version")]
    pub filling_tool_version: Option<String>,
    #[serde(rename = "filling-transition-tool")]
    pub filling_transition_tool: Option<String>,
    pub generated_test_hash: Option<String>,
    pub hash: Option<String>,
    pub labels: Option<BTreeMap<String, String>>,
    pub lllcversion: Option<String>,
    pub solidity: Option<String>,
    pub source: Option<String>,
    pub source_hash: Option<String>,
    pub url: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct EthereumTestEnvironment {
    pub current_base_fee: Option<U256>,
    pub current_coinbase: Address,
    pub current_difficulty: U256,
    pub current_excess_blob_gas: Option<U64>,
    pub current_gas_limit: U64,
    pub current_number: U64,
    pub current_random: Option<B256>,
    pub current_timestamp: U64,
    pub previous_hash: Option<B256>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EthereumTestAccount {
    pub balance: U256,
    pub code: Bytes,
    pub nonce: U64,
    pub storage: HashMap<B256, B256>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct EthereumTestTransaction {
    pub data: Vec<Bytes>,
    pub gas_limit: Vec<U64>,
    pub gas_price: Option<U256>,
    pub max_fee_per_gas: Option<U256>,
    pub max_priority_fee_per_gas: Option<U256>,
    pub max_fee_per_blob_gas: Option<U256>,
    pub nonce: U64,
    pub secret_key: B256,
    pub sender: Address,
    pub to: String,
    pub value: Vec<U256>,
    pub access_lists: Option<Vec<Vec<EthereumTestAccessListEntry>>>,
    pub blob_versioned_hashes: Option<Vec<B256>>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct EthereumTestAccessListEntry {
    pub address: Address,
    pub storage_keys: Vec<B256>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
pub enum EthereumTestFork {
    Cancun,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct EthereumTestPostState {
    pub hash: B256,
    pub indexes: EthereumTestTransactionIndexes,
    pub logs: B256,
    pub txbytes: Bytes,
    pub expect_exception: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct EthereumTestTransactionIndexes {
    pub data: usize,
    pub gas: usize,
    pub value: usize,
}
