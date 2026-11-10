use alloy_consensus::TxEnvelope;
use alloy_eips::eip2718::Decodable2718;
use alloy_primitives::keccak256;
use monad_ethcall::{ffi::PoolConfig, EthSimulateSuccess, MonadExecutor};

use self::fixture::EthereumTestPostState;
pub use self::fixture::{EthereumTestCase, EthereumTestFork};

mod fixture;
mod simulate;

pub static ETHEREUM_TESTS: include_dir::Dir<'static> = include_dir::include_dir!(
    "$CARGO_MANIFEST_DIR/../../../third_party/ethereum-tests/GeneralStateTests/stChainId"
);

pub struct ExecEventEthereumTestValidator {
    executor: MonadExecutor,
}

impl ExecEventEthereumTestValidator {
    pub fn new() -> Self {
        let pool_config = PoolConfig {
            num_threads: 1,
            num_fibers: 2,
            timeout_sec: 1,
            queue_limit: 1000,
        };
        let executor = MonadExecutor::new_null_db(pool_config, pool_config, pool_config, 1, 0);

        Self { executor }
    }

    pub async fn validate(&self, test: EthereumTestCase) {
        let EthereumTestCase {
            info: _,
            env,
            pre,
            transaction,
            post,
        } = test;

        for EthereumTestPostState {
            hash: expected_hash,
            indexes,
            logs: expected_logs,
            txbytes: expected_txbytes,
            expect_exception: expected_exception,
        } in post.into_values().flatten()
        {
            let actual = simulate::simulate_ethereum_test(
                &self.executor,
                env.clone(),
                pre.clone(),
                transaction.clone(),
                indexes,
            )
            .await;

            // let actual_header = actual.to_alloy_header();
            // assert_eq!(
            //     actual_header.state_root, expected_hash,
            //     "Ethereum test hash mismatch"
            // );

            let logs = actual
                .txns
                .iter()
                .flat_map(|transaction| transaction.to_alloy_logs())
                .collect::<Vec<_>>();
            assert_eq!(keccak256(alloy_rlp::encode(logs)), expected_logs);

            let expected_transaction = TxEnvelope::decode_2718(&mut expected_txbytes.as_ref())
                .expect("invalid expected transaction bytes");
            assert_eq!(actual.txns.len(), 1);
            assert_eq!(expected_transaction, actual.txns[0].to_alloy());

            assert_eq!(expected_exception, None);
        }
    }
}
