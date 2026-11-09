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

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PreStateTracerConfig {
    pub diff_mode: bool,
    pub disable_code: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MonadTracer {
    NoopTracer,
    CallTracer,
    PreStateTracer(PreStateTracerConfig),
    AccessListTracer,
}

impl MonadTracer {
    fn to_ffi_tracer_config(self) -> ffi::monad_tracer_config {
        match self {
            Self::NoopTracer => ffi::monad_tracer_config_NOOP_TRACER,
            Self::CallTracer => ffi::monad_tracer_config_CALL_TRACER,
            Self::PreStateTracer(_) => ffi::monad_tracer_config_PRESTATE_TRACER,
            Self::AccessListTracer => ffi::monad_tracer_config_ACCESS_LIST_TRACER,
        }
    }

    fn to_ffi_prestate_tracer_config(self) -> ffi::monad_prestate_tracer_config {
        let PreStateTracerConfig {
            diff_mode,
            disable_code,
        } = match self {
            Self::PreStateTracer(config) => config,
            _ => PreStateTracerConfig::default(),
        };
        ffi::monad_prestate_tracer_config {
            diff_mode,
            disable_code,
        }
    }
}
