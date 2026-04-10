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

pub use self::bindings::monad_executor_pool_config as PoolConfig;
pub(crate) use self::bindings::{
    add_override_address, monad_chain_config, monad_chain_config_CHAIN_CONFIG_ETHEREUM_MAINNET,
    monad_chain_config_CHAIN_CONFIG_MONAD_DEVNET, monad_chain_config_CHAIN_CONFIG_MONAD_MAINNET,
    monad_chain_config_CHAIN_CONFIG_MONAD_TESTNET, monad_executor, monad_executor_create,
    monad_executor_destroy, monad_executor_eth_call_submit, monad_executor_result,
    monad_executor_result_release, monad_executor_run_transactions, monad_state_override_create,
    monad_state_override_destroy, monad_tracer_config_NOOP_TRACER, set_override_balance,
    set_override_code, set_override_nonce, set_override_state, set_override_state_diff,
};

#[allow(dead_code, non_camel_case_types, non_upper_case_globals)]
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
