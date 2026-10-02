// Copyright (C) 2025 Category Labs, Inc.
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

pub use self::executor::*;

mod executor;
pub mod ffi;
pub mod overrides;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ChainId {
    EthereumMainnet,
    MonadMainnet,
    MonadTestnet,
    MonadDevnet,
    HiveNet,
}

impl ChainId {
    fn to_ffi_chain_config(self) -> ffi::monad_chain_config {
        match self {
            Self::EthereumMainnet => ffi::monad_chain_config_CHAIN_CONFIG_ETHEREUM_MAINNET,
            Self::MonadMainnet => ffi::monad_chain_config_CHAIN_CONFIG_MONAD_MAINNET,
            Self::MonadTestnet => ffi::monad_chain_config_CHAIN_CONFIG_MONAD_TESTNET,
            Self::MonadDevnet => ffi::monad_chain_config_CHAIN_CONFIG_MONAD_DEVNET,
            Self::HiveNet => ffi::monad_chain_config_CHAIN_CONFIG_HIVE_NET,
        }
    }
}

/// Optional header fields a block carries; each variant adds to the previous
/// one, so they are ordered.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub enum EthHeaderLayout {
    /// No optional fields.
    Legacy,
    /// Adds `base_fee_per_gas` (EIP-1559).
    London,
    /// Adds `withdrawals_root` (EIP-4895).
    Shanghai,
    /// Adds `blob_gas_used` and `excess_blob_gas` (EIP-4844) and
    /// `parent_beacon_block_root` (EIP-4788).
    Cancun,
    /// Adds `requests_hash` (EIP-7685).
    Prague,
    /// Adds `block_access_list_hash` (EIP-7928) and `slot_number` (EIP-7843).
    Amsterdam,
}

impl EthHeaderLayout {
    fn from_ffi(layout: ffi::monad_eth_header_layout) -> Option<Self> {
        match layout {
            ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_LEGACY => Some(Self::Legacy),
            ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_LONDON => Some(Self::London),
            ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_SHANGHAI => Some(Self::Shanghai),
            ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_CANCUN => Some(Self::Cancun),
            ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_PRAGUE => Some(Self::Prague),
            ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_AMSTERDAM => Some(Self::Amsterdam),
            _ => None,
        }
    }
}

/// An executed (non-genesis) block's header layout per execution's validator;
/// `None` when execution cannot say, in which case leave the header as built.
pub fn eth_header_layout(
    chain: ChainId,
    block_number: u64,
    timestamp: u64,
) -> Option<EthHeaderLayout> {
    EthHeaderLayout::from_ffi(unsafe {
        ffi::monad_chain_eth_header_layout(chain.to_ffi_chain_config(), block_number, timestamp)
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum MonadTracer {
    NoopTracer = 0,
    CallTracer,
    PreStateTracer,
    StateDiffTracer,
    AccessListTracer,
}

impl From<MonadTracer> for u32 {
    fn from(tracer: MonadTracer) -> u32 {
        match tracer {
            MonadTracer::NoopTracer => 0,
            MonadTracer::CallTracer => 1,
            MonadTracer::PreStateTracer => 2,
            MonadTracer::StateDiffTracer => 3,
            MonadTracer::AccessListTracer => 4,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eth_header_layout_from_ffi_constants() {
        assert_eq!(
            EthHeaderLayout::from_ffi(ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_LEGACY),
            Some(EthHeaderLayout::Legacy)
        );
        assert_eq!(
            EthHeaderLayout::from_ffi(ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_LONDON),
            Some(EthHeaderLayout::London)
        );
        assert_eq!(
            EthHeaderLayout::from_ffi(
                ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_SHANGHAI
            ),
            Some(EthHeaderLayout::Shanghai)
        );
        assert_eq!(
            EthHeaderLayout::from_ffi(ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_CANCUN),
            Some(EthHeaderLayout::Cancun)
        );
        assert_eq!(
            EthHeaderLayout::from_ffi(ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_PRAGUE),
            Some(EthHeaderLayout::Prague)
        );
        assert_eq!(
            EthHeaderLayout::from_ffi(
                ffi::monad_eth_header_layout_MONAD_ETH_HEADER_LAYOUT_AMSTERDAM
            ),
            Some(EthHeaderLayout::Amsterdam)
        );
        assert_eq!(EthHeaderLayout::from_ffi(99), None);
    }

    #[test]
    fn eth_header_layout_is_ordered() {
        assert!(EthHeaderLayout::Legacy < EthHeaderLayout::London);
        assert!(EthHeaderLayout::London < EthHeaderLayout::Shanghai);
        assert!(EthHeaderLayout::Shanghai < EthHeaderLayout::Cancun);
        assert!(EthHeaderLayout::Cancun < EthHeaderLayout::Prague);
        assert!(EthHeaderLayout::Prague < EthHeaderLayout::Amsterdam);
    }

    #[test]
    fn eth_header_layout_queries_execution() {
        // The exec-events replay fixture block.
        assert_eq!(
            eth_header_layout(ChainId::EthereumMainnet, 15_000_001, 1655778552),
            Some(EthHeaderLayout::London)
        );
        // Below the Berlin floor.
        assert_eq!(eth_header_layout(ChainId::EthereumMainnet, 0, 0), None);
        assert_eq!(
            eth_header_layout(ChainId::MonadMainnet, 1, 0),
            Some(EthHeaderLayout::Cancun)
        );
    }
}
