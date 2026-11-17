// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use alloy_eips::{Encodable2718, Typed2718};
use alloy_network::ReceiptResponse;
use alloy_primitives::{keccak256, B256};
use alloy_provider::Provider;
use monad_alloy::provider_builder;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        return Err("usage: inspect RPC_URL TRANSACTION_HASH".into());
    }
    let hash: B256 = args[2].parse()?;
    let provider = provider_builder().connect_http(args[1].parse()?);
    let tx = provider
        .get_transaction_by_hash(hash)
        .await?
        .ok_or("transaction not found")?;
    let envelope = tx.inner.inner();
    let canonical_hash = keccak256(envelope.encoded_2718());
    if canonical_hash != hash || envelope.recover_signer()? != tx.inner.signer() {
        return Err("transaction hash or sender mismatch".into());
    }
    let Some(receipt) = provider.get_transaction_receipt(hash).await? else {
        println!("Pending: type=0x{:x}, hash={canonical_hash}", envelope.ty());
        return Ok(());
    };
    if receipt.transaction_hash != hash || receipt.inner.ty() != envelope.ty() {
        return Err("receipt hash or type mismatch".into());
    }
    let block_hash = receipt.block_hash.ok_or("receipt has no block hash")?;
    if tx.block_hash != Some(block_hash) || tx.block_number != receipt.block_number {
        return Err("transaction and receipt inclusion metadata differ; retry after mining".into());
    }
    let block = provider
        .get_block_by_hash(block_hash)
        .full()
        .await?
        .ok_or("receipt block not found")?;
    let included = block
        .transactions
        .as_transactions()
        .ok_or("expected full block")?;
    let index: usize = receipt
        .transaction_index
        .ok_or("receipt has no transaction index")?
        .try_into()?;
    let block_tx = included
        .get(index)
        .ok_or("transaction index outside block")?;
    if block_tx.inner.inner().encoded_2718() != envelope.encoded_2718() {
        return Err("block transaction differs from lookup".into());
    }
    println!(
        "Verified: type=0x{:x}, hash={canonical_hash}, block={block_hash}, success={}",
        envelope.ty(),
        receipt.status()
    );
    Ok(())
}
