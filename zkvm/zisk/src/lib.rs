// Copyright (C) 2025-26 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

//! Monad's Ethereum mainnet witness executor for ZisK.
//!
//! Host builds cross-compile the guest and expose its ELF. On the ZisK target,
//! the library links the C++ executor called by this package's guest binary.

#![cfg_attr(all(target_os = "zkvm", target_vendor = "zisk"), no_std)]

#[cfg(not(all(target_os = "zkvm", target_vendor = "zisk")))]
pub const ELF: zisk_sdk::GuestProgram = zisk_sdk::GuestProgram::from_static(
    "zec-monad",
    env!("MONAD_GUEST_ELF_HASH"),
    include_bytes!(env!("MONAD_GUEST_ELF")),
);

/// Execute the input witness and write the resulting block hash.
#[cfg(all(target_os = "zkvm", target_vendor = "zisk"))]
pub fn execute_witness() {
    extern "C" {
        fn monad_zkvm_execute_witness();
    }
    unsafe { monad_zkvm_execute_witness() };
}
