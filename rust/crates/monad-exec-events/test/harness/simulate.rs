use std::collections::BTreeMap;

use alloy_consensus::{
    transaction::TxHashable, Header, SignableTransaction, Signed, TxEip1559, TxEip2930, TxEnvelope,
    TxLegacy,
};
use alloy_eips::eip7685::EMPTY_REQUESTS_HASH;
use alloy_primitives::{Address, Bytes, Signature, TxKind, B256, U256};
use k256::ecdsa::{signature::hazmat::PrehashSigner, SigningKey};
use monad_ethcall::{
    overrides::{BlockOverride, StateOverrideObject, StateOverrideSet, StorageOverride},
    ChainId, EthSimulateSuccess, MonadExecutor,
};
use monad_event_ring::{DecodedEventRing, EventNextResult};
use monad_exec_events::{
    BlockBuilderError, ExecEphemeralEventRing, ExecutedBlock, ExecutedBlockBuilder,
};

use super::fixture::{
    EthereumTestAccount, EthereumTestEnvironment, EthereumTestTransaction,
    EthereumTestTransactionIndexes,
};

const HIVENET_CHAIN_ID: u64 = 3503995874084926;

pub async fn simulate_ethereum_test(
    executor: &MonadExecutor,
    env: EthereumTestEnvironment,
    pre: BTreeMap<Address, EthereumTestAccount>,
    transaction: EthereumTestTransaction,
    indexes: EthereumTestTransactionIndexes,
) -> ExecutedBlock {
    let EthereumTestEnvironment {
        current_base_fee,
        current_coinbase,
        current_difficulty,
        current_excess_blob_gas,
        current_gas_limit,
        current_number,
        current_random,
        current_timestamp,
        previous_hash,
    } = env;

    assert!(current_excess_blob_gas.is_none_or(|gas| gas == 0));

    let block_header = Header {
        parent_hash: previous_hash.unwrap_or(B256::ZERO),
        ommers_hash: B256::ZERO,
        beneficiary: current_coinbase,
        state_root: B256::ZERO,
        transactions_root: B256::ZERO,
        receipts_root: B256::ZERO,
        logs_bloom: alloy_primitives::Bloom::ZERO,
        difficulty: current_difficulty,
        number: current_number.try_into().unwrap(),
        gas_limit: current_gas_limit.try_into().unwrap(),
        gas_used: 0,
        timestamp: current_timestamp.try_into().unwrap(),
        extra_data: alloy_primitives::Bytes::new(),
        mix_hash: current_random.unwrap_or(B256::ZERO),
        nonce: alloy_primitives::B64::ZERO,
        base_fee_per_gas: current_base_fee.map(|base_fee: U256| base_fee.try_into().unwrap()),
        withdrawals_root: Some(B256::ZERO),
        blob_gas_used: Some(0),
        excess_blob_gas: Some(0),
        parent_beacon_block_root: Some(B256::ZERO),
        requests_hash: Some(EMPTY_REQUESTS_HASH),
        block_access_list_hash: None,
        slot_number: None,
    };

    let EthereumTestTransaction {
        data,
        gas_limit,
        gas_price,
        max_fee_per_gas,
        max_priority_fee_per_gas,
        max_fee_per_blob_gas,
        nonce,
        secret_key,
        sender,
        to,
        value,
        access_lists,
        blob_versioned_hashes,
    } = transaction;

    assert!(
        max_fee_per_blob_gas.is_none(),
        "EIP-4844 transactions are unsupported"
    );
    assert!(
        blob_versioned_hashes.is_none(),
        "blob transactions are unsupported"
    );

    let signing_key = SigningKey::from_bytes((&secret_key.0).into()).unwrap();

    let mut calls = Vec::new();

    let data_index = indexes.data;
    let input = &data[indexes.data];
    let gas_limit = &gas_limit[indexes.gas];
    let value = &value[indexes.value];
    let to = if to.is_empty() {
        TxKind::Create
    } else {
        TxKind::Call(to.parse::<Address>().unwrap())
    };

    let access_list = access_lists.as_ref().map(|lists| {
        let entries = lists.get(data_index).map(Vec::as_slice).unwrap_or_default();

        alloy_rpc_types::AccessList(
            entries
                .iter()
                .map(|entry| alloy_rpc_types::AccessListItem {
                    address: entry.address,
                    storage_keys: entry.storage_keys.clone(),
                })
                .collect(),
        )
    });

    let call = match (max_fee_per_gas, max_priority_fee_per_gas, access_list) {
        (Some(max_fee_per_gas), Some(max_priority_fee_per_gas), Some(access_list)) => {
            let mut unsigned = TxEip1559 {
                chain_id: HIVENET_CHAIN_ID,
                nonce: nonce.try_into().unwrap(),
                gas_limit: (*gas_limit).try_into().unwrap(),
                max_fee_per_gas: max_fee_per_gas.try_into().unwrap(),
                max_priority_fee_per_gas: max_priority_fee_per_gas.try_into().unwrap(),
                to,
                value: *value,
                access_list,
                input: input.clone(),
            };
            let signature = sign(&mut unsigned, &signing_key);
            TxEnvelope::Eip1559(unsigned.into_signed(signature))
        }
        (None, _, Some(access_list)) => {
            let mut unsigned = TxEip2930 {
                chain_id: HIVENET_CHAIN_ID,
                nonce: nonce.try_into().unwrap(),
                gas_limit: (*gas_limit).try_into().unwrap(),
                gas_price: gas_price
                    .expect("EIP-2930 transaction has no gas price")
                    .try_into()
                    .unwrap(),
                to,
                value: *value,
                access_list,
                input: input.clone(),
            };
            let signature = sign(&mut unsigned, &signing_key);
            TxEnvelope::Eip2930(unsigned.into_signed(signature))
        }
        (None, _, None) => {
            let mut unsigned = TxLegacy {
                chain_id: None,
                nonce: nonce.try_into().unwrap(),
                gas_price: gas_price
                    .expect("legacy transaction has no gas price")
                    .try_into()
                    .unwrap(),
                gas_limit: (*gas_limit).try_into().unwrap(),
                to,
                value: *value,
                input: input.clone(),
            };
            let signature = sign(&mut unsigned, &signing_key);
            TxEnvelope::Legacy(unsigned.into_signed(signature))
        }
        (Some(max_fee_per_gas), Some(max_priority_fee_per_gas), None) => {
            let mut unsigned = TxEip1559 {
                chain_id: HIVENET_CHAIN_ID,
                nonce: nonce.try_into().unwrap(),
                gas_limit: (*gas_limit).try_into().unwrap(),
                max_fee_per_gas: max_fee_per_gas.try_into().unwrap(),
                max_priority_fee_per_gas: max_priority_fee_per_gas.try_into().unwrap(),
                to,
                value: *value,
                access_list: Default::default(),
                input: input.clone(),
            };
            let signature = sign(&mut unsigned, &signing_key);
            TxEnvelope::Eip1559(unsigned.into_signed(signature))
        }
        (Some(_), None, _) => panic!("EIP-1559 transaction has no priority fee"),
    };
    calls.push(vec![call]);

    let mut state_override = pre
        .into_iter()
        .map(|(address, account)| {
            (
                address,
                StateOverrideObject {
                    balance: Some(account.balance),
                    nonce: Some(account.nonce),
                    code: Some(account.code),
                    storage_override: Some(StorageOverride::State(account.storage)),
                },
            )
        })
        .collect::<StateOverrideSet>();
    for address in [
        "0x00000961ef480eb55e80d19ad83579a64c007002"
            .parse::<Address>()
            .unwrap(),
        "0x0000bbddc7ce488642fb579f8b00f3a590007251"
            .parse::<Address>()
            .unwrap(),
    ] {
        state_override.entry(address).or_default().code =
            Some(Bytes::from_static(&[0x5f, 0x5f, 0xf3]));
    }

    let overrides = (0..calls.len())
        .map(|_| (BlockOverride::default(), state_override.clone()))
        .collect::<Vec<_>>();

    let override_refs = overrides
        .iter()
        .map(|(block, state)| (block, state))
        .collect::<Vec<_>>();

    let event_ring = ExecEphemeralEventRing::new_with_schema(24, 32, &unsafe {
        monad_exec_events::ffi::g_monad_exec_event_schema_hash
    })
    .unwrap();

    let mut reader = event_ring.create_reader();

    executor
        .eth_simulate_v1(
            ChainId::HiveNet,
            &vec![vec![sender]; calls.len()],
            &calls,
            block_header,
            current_number.as_limbs()[0],
            None,
            None,
            current_gas_limit.as_limbs()[0],
            usize::MAX,
            usize::MAX,
            false,
            Some(&event_ring),
            &override_refs,
        )
        .await
        .unwrap();

    let mut builder = ExecutedBlockBuilder::new(true);

    loop {
        let descriptor = match reader.next_descriptor() {
            EventNextResult::Ready(descriptor) => descriptor,
            EventNextResult::NotReady => panic!("ephemeral event ring did not produce block"),
            EventNextResult::Gap => panic!("ephemeral event ring produced a gap"),
        };

        let Some(result) = builder.process_event_descriptor(&descriptor) else {
            continue;
        };

        match result {
            Ok(block) => {
                assert!(matches!(
                    reader.next_descriptor(),
                    EventNextResult::NotReady
                ));

                return block;
            }
            Err(BlockBuilderError::Rejected) => panic!("simulation rejected the block"),
            Err(BlockBuilderError::PayloadExpired) => panic!("simulation event payload expired"),
            Err(BlockBuilderError::ImplicitDrop { .. }) => {
                panic!("simulation produced an unterminated block")
            }
        }
    }
}

fn sign<T: SignableTransaction<Signature> + TxHashable<Signature>>(
    transaction: &mut T,
    key: &SigningKey,
) -> Signature {
    let (signature, recovery_id) = key
        .sign_prehash_recoverable(transaction.signature_hash().as_slice())
        .unwrap();
    Signature::from_signature_and_parity(signature, recovery_id.is_y_odd())
}
