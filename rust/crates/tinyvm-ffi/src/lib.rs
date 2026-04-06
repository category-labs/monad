//! TinyVM generic FFI bridge.
//!
//! Single entry point `tinyvm_apply` that delegates to the Rust backend registry.
//! The C++ precompile calls this; Rust drives state reads/writes via callbacks.

use std::ffi::c_void;
use std::slice;

use anyhow::{anyhow, ensure};
use tiny_privacy_vm_confidential_backend::ConfidentialTinyVmBackend;
use tiny_privacy_vm_confidential_backend::CONFIDENTIAL_BACKEND_ID;
use tiny_privacy_vm_runtime::{
    TinyVmArtifact, TinyVmBackend, TinyVmCall, TinyVmOperation, TinyVmRegistry,
    TinyVmStateStore, TinyVmTokenRegistration, TinyVmTxContext,
    TINYVM_CALL_MAGIC, decode_tinyvm_artifacts, encode_tinyvm_call,
};

// ── Callback-backed store ───────────────────────────────────────────────────

type StoreGetFn = unsafe extern "C" fn(
    ctx: *mut c_void,
    key: *const u8, key_len: usize,
    value_buf: *mut u8, value_buf_len: usize,
    value_len: *mut usize,
) -> i32;

type StoreSetFn = unsafe extern "C" fn(
    ctx: *mut c_void,
    key: *const u8, key_len: usize,
    value: *const u8, value_len: usize,
);

struct FfiStore {
    ctx: *mut c_void,
    get_fn: StoreGetFn,
    set_fn: StoreSetFn,
}

impl TinyVmStateStore for FfiStore {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>> {
        let mut buf = vec![0u8; 4096];
        let mut len: usize = 0;
        let rc = unsafe {
            (self.get_fn)(
                self.ctx,
                key.as_ptr(), key.len(),
                buf.as_mut_ptr(), buf.len(),
                &mut len,
            )
        };
        if rc != 1 || len == 0 {
            return None;
        }
        buf.truncate(len);
        // Check if all zeros (EVM default = not set)
        if buf.iter().all(|&b| b == 0) {
            return None;
        }
        Some(buf)
    }

    fn set(&mut self, key: &[u8], value: &[u8]) {
        unsafe {
            (self.set_fn)(
                self.ctx,
                key.as_ptr(), key.len(),
                value.as_ptr(), value.len(),
            );
        }
    }
}

// ── Result struct ───────────────────────────────────────────────────────────

#[repr(C)]
pub struct TinyVmApplyResult {
    pub escrow_refund: u128,
    pub token: [u8; 32],
    pub owner: [u8; 20],
    pub success: u8,
}

// ── Registry ────────────────────────────────────────────────────────────────

fn registry() -> TinyVmRegistry<'static> {
    static BACKEND: ConfidentialTinyVmBackend = ConfidentialTinyVmBackend;
    static BACKENDS: [&dyn TinyVmBackend; 1] = [&BACKEND];
    TinyVmRegistry::new(&BACKENDS)
}

// ── ABI compatibility bridge ───────────────────────────────────────────────

const REGISTER_TOKEN_SELECTOR: [u8; 4] = [0x2d, 0xed, 0x0f, 0xb5];
const SHIELD_PUBLIC_SELECTOR: [u8; 4] = [0xaf, 0xac, 0xd7, 0x77];
const TRANSFER_CONFIDENTIAL_SELECTOR: [u8; 4] = [0xf2, 0x4b, 0xf2, 0x0e];
const UNSHIELD_PUBLIC_SELECTOR: [u8; 4] = [0x5b, 0xd2, 0x62, 0xb4];

fn decode_abi_usize(word: &[u8]) -> anyhow::Result<usize> {
    ensure!(word.len() == 32, "abi word must be 32 bytes");
    ensure!(word[..24].iter().all(|b| *b == 0), "abi integer too large");

    let mut low = [0u8; 8];
    low.copy_from_slice(&word[24..32]);
    Ok(u64::from_be_bytes(low) as usize)
}

fn decode_abi_bytes(args: &[u8], offset: usize) -> anyhow::Result<Vec<u8>> {
    ensure!(offset + 32 <= args.len(), "abi offset out of range");

    let len = decode_abi_usize(&args[offset..offset + 32])?;
    let data_offset = offset + 32;
    let padded_len = len
        .checked_add(31)
        .ok_or_else(|| anyhow!("abi length overflow"))?
        / 32
        * 32;

    ensure!(data_offset + padded_len <= args.len(), "abi bytes truncated");
    Ok(args[data_offset..data_offset + len].to_vec())
}

fn decode_abi_two_bytes(args: &[u8]) -> anyhow::Result<(Vec<u8>, Vec<u8>)> {
    ensure!(args.len() >= 64, "abi head too short");

    let first_offset = decode_abi_usize(&args[..32])?;
    let second_offset = decode_abi_usize(&args[32..64])?;

    Ok((
        decode_abi_bytes(args, first_offset)?,
        decode_abi_bytes(args, second_offset)?,
    ))
}

fn encode_internal_call(
    operation: TinyVmOperation,
    public_args: Vec<u8>,
    artifacts: Vec<TinyVmArtifact>,
) -> Vec<u8> {
    encode_tinyvm_call(&TinyVmCall {
        backend_id: CONFIDENTIAL_BACKEND_ID,
        operation,
        public_args,
        artifacts,
    })
}

fn normalize_detached_abi_call(input: &[u8]) -> anyhow::Result<Vec<u8>> {
    ensure!(input.len() >= 4, "payload shorter than selector");

    let selector: [u8; 4] = input[..4]
        .try_into()
        .expect("slice length checked above");
    let args = &input[4..];

    match selector {
        REGISTER_TOKEN_SELECTOR => {
            ensure!(args.len() >= 64, "registerToken args too short");
            ensure!(
                args[32..44].iter().all(|b| *b == 0),
                "registerToken address must be left-padded"
            );

            let mut token = [0u8; 32];
            token.copy_from_slice(&args[..32]);

            let mut public_asset = [0u8; 20];
            public_asset.copy_from_slice(&args[44..64]);

            let public_args = bincode::serialize(&TinyVmTokenRegistration {
                token,
                public_asset,
            })?;
            Ok(encode_internal_call(
                TinyVmOperation::RegisterToken,
                public_args,
                vec![],
            ))
        }
        SHIELD_PUBLIC_SELECTOR => {
            let (tx_bytes, artifacts_bytes) = decode_abi_two_bytes(args)?;
            let artifacts = decode_tinyvm_artifacts(&artifacts_bytes)?;
            Ok(encode_internal_call(
                TinyVmOperation::Shield,
                tx_bytes,
                artifacts,
            ))
        }
        TRANSFER_CONFIDENTIAL_SELECTOR => {
            let (tx_bytes, artifacts_bytes) = decode_abi_two_bytes(args)?;
            let artifacts = decode_tinyvm_artifacts(&artifacts_bytes)?;
            Ok(encode_internal_call(
                TinyVmOperation::Transfer,
                tx_bytes,
                artifacts,
            ))
        }
        UNSHIELD_PUBLIC_SELECTOR => {
            let (tx_bytes, artifacts_bytes) = decode_abi_two_bytes(args)?;
            let artifacts = decode_tinyvm_artifacts(&artifacts_bytes)?;
            Ok(encode_internal_call(
                TinyVmOperation::Unshield,
                tx_bytes,
                artifacts,
            ))
        }
        _ => Err(anyhow!("unknown tinyvm selector")),
    }
}

fn normalize_input(input: &[u8]) -> anyhow::Result<Vec<u8>> {
    if input.starts_with(&TINYVM_CALL_MAGIC) {
        return Ok(input.to_vec());
    }

    normalize_detached_abi_call(input)
}

// ── FFI entry points ────────────────────────────────────────────────────────

/// Returns gas cost for the given TinyVM call input, or 0 on decode failure.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn tinyvm_gas_cost(
    input: *const u8, input_len: usize,
) -> u64 {
    let input_slice = unsafe { slice::from_raw_parts(input, input_len) };
    let normalized = match normalize_input(input_slice) {
        Ok(normalized) => normalized,
        Err(_) => return 0,
    };
    registry().gas_cost(&normalized).unwrap_or(0)
}

/// Generic TinyVM entry point called by the C++ precompile.
/// Decodes envelope, dispatches to backend, verifies + applies state.
/// Logs are serialized into logs_buf as a flat binary format.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn tinyvm_apply(
    sender: *const u8, sender_len: usize,
    // TODO: pass tx_value as raw 32 bytes (u256) and let the backend handle truncation
    tx_value_lo: u64, tx_value_hi: u64,
    input: *const u8, input_len: usize,
    store_ctx: *mut c_void,
    store_get: StoreGetFn,
    store_set: StoreSetFn,
    result: *mut TinyVmApplyResult,
    logs_buf: *mut u8, logs_buf_len: usize, logs_written: *mut usize,
    error_buf: *mut u8, error_len: usize,
) -> i32 {
    let sender_slice = unsafe { slice::from_raw_parts(sender, sender_len) };
    let input_slice = unsafe { slice::from_raw_parts(input, input_len) };
    let normalized_input = match normalize_input(input_slice) {
        Ok(normalized) => normalized,
        Err(err) => {
            let msg = format!("{err:#}");
            let bytes = msg.as_bytes();
            let copy_len = bytes.len().min(error_len.saturating_sub(1));
            unsafe {
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), error_buf, copy_len);
                *error_buf.add(copy_len) = 0;
                (*result).success = 0;
                *logs_written = 0;
            }
            return 0;
        }
    };

    let mut sender_arr = [0u8; 20];
    if sender_len >= 20 {
        sender_arr.copy_from_slice(&sender_slice[..20]);
    }

    let ctx = TinyVmTxContext {
        sender: sender_arr,
        tx_value: (tx_value_lo as u128) | ((tx_value_hi as u128) << 64),
    };

    let mut store = FfiStore {
        ctx: store_ctx,
        get_fn: store_get,
        set_fn: store_set,
    };

    match registry().apply_input(&ctx, &normalized_input, &mut store) {
        Ok(decoded) => {
            unsafe {
                (*result).success = 1;
                (*result).escrow_refund = decoded.metadata.as_ref().map_or(0u128, |m| m.escrow_refund);

                // Populate token and owner from access_keys for escrow refund
                if let Some(meta) = &decoded.metadata {
                    for key in &meta.access_keys {
                        match key {
                            tiny_privacy_vm_runtime::TinyVmAccessKey::Account { token, owner } => {
                                (*result).token.copy_from_slice(token);
                                (*result).owner.copy_from_slice(owner);
                                break; // first account key is the primary owner
                            }
                            tiny_privacy_vm_runtime::TinyVmAccessKey::Token { token } => {
                                (*result).token.copy_from_slice(token);
                            }
                        }
                    }
                }

                // Serialize logs into output buffer
                if let Some(meta) = &decoded.metadata {
                    let serialized = serialize_logs(&meta.logs);
                    let copy_len = serialized.len().min(logs_buf_len);
                    if copy_len > 0 {
                        std::ptr::copy_nonoverlapping(serialized.as_ptr(), logs_buf, copy_len);
                    }
                    *logs_written = copy_len;
                } else {
                    *logs_written = 0;
                }
            }
            1
        }
        Err(err) => {
            let msg = format!("{err:#}");
            let bytes = msg.as_bytes();
            let copy_len = bytes.len().min(error_len.saturating_sub(1));
            unsafe {
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), error_buf, copy_len);
                *error_buf.add(copy_len) = 0;
                (*result).success = 0;
                *logs_written = 0;
            }
            0
        }
    }
}

/// Serialize logs to a flat binary format:
///   [num_logs: u32 LE]
///   for each log:
///     [num_topics: u32 LE] [topic0..topicN: 32 bytes each]
///     [data_len: u32 LE] [data: data_len bytes]
fn serialize_logs(logs: &[tiny_privacy_vm_runtime::TinyVmLog]) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(&(logs.len() as u32).to_le_bytes());
    for log in logs {
        buf.extend_from_slice(&(log.topics.len() as u32).to_le_bytes());
        for topic in &log.topics {
            buf.extend_from_slice(topic);
        }
        buf.extend_from_slice(&(log.data.len() as u32).to_le_bytes());
        buf.extend_from_slice(&log.data);
    }
    buf
}

// ── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use std::sync::Mutex;

    use tiny_privacy_vm_confidential_backend::{
        CryptoConfig, native_mon_public_asset, sample_token,
        new_empty_local_account, prove_shield_public,
        prove_transfer_with_sidecars, prove_unshield_public,
        apply_encrypted_recipient_memo, generate_auditor_keypair,
        serialize_public_balance_change_tx_bytes,
        serialize_public_balance_change_artifacts,
        serialize_transfer_tx_bytes, serialize_transfer_artifacts,
        AccountState,
    };
    use tiny_privacy_vm_runtime::encode_tinyvm_artifacts;

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// ABI-encode two bytes values: abi.encode(bytes, bytes)
    fn abi_encode_two_bytes(a: &[u8], b: &[u8]) -> Vec<u8> {
        fn pad32(len: usize) -> usize { ((len + 31) / 32) * 32 }
        fn word(val: usize) -> [u8; 32] {
            let mut w = [0u8; 32];
            w[24..].copy_from_slice(&(val as u64).to_be_bytes());
            w
        }

        let a_padded = pad32(a.len());
        let b_padded = pad32(b.len());

        // offset_a = 64 (two words of head)
        // offset_b = 64 + 32 + a_padded
        let offset_a = 64usize;
        let offset_b = offset_a + 32 + a_padded;

        let mut out = Vec::new();
        out.extend_from_slice(&word(offset_a));
        out.extend_from_slice(&word(offset_b));
        out.extend_from_slice(&word(a.len()));
        out.extend_from_slice(a);
        out.extend_from_slice(&vec![0u8; a_padded - a.len()]);
        out.extend_from_slice(&word(b.len()));
        out.extend_from_slice(b);
        out.extend_from_slice(&vec![0u8; b_padded - b.len()]);
        out
    }

    fn build_shield_calldata(bundle: &tiny_privacy_vm_confidential_backend::PublicBalanceChangeBundle) -> Vec<u8> {
        let tx_bytes = serialize_public_balance_change_tx_bytes(&bundle.public);
        let artifacts = encode_tinyvm_artifacts(&serialize_public_balance_change_artifacts(&bundle.proof));
        let mut cd = Vec::from(SHIELD_PUBLIC_SELECTOR);
        cd.extend(abi_encode_two_bytes(&tx_bytes, &artifacts));
        cd
    }

    fn build_transfer_calldata(tc: &tiny_privacy_vm_confidential_backend::TransferCall) -> Vec<u8> {
        let tx_bytes = serialize_transfer_tx_bytes(&tc.bundle.public);
        let artifacts = encode_tinyvm_artifacts(&serialize_transfer_artifacts(&tc.bundle.proof, &tc.sidecars));
        let mut cd = Vec::from(TRANSFER_CONFIDENTIAL_SELECTOR);
        cd.extend(abi_encode_two_bytes(&tx_bytes, &artifacts));
        cd
    }

    fn build_unshield_calldata(bundle: &tiny_privacy_vm_confidential_backend::PublicBalanceChangeBundle) -> Vec<u8> {
        let tx_bytes = serialize_public_balance_change_tx_bytes(&bundle.public);
        let artifacts = encode_tinyvm_artifacts(&serialize_public_balance_change_artifacts(&bundle.proof));
        let mut cd = Vec::from(UNSHIELD_PUBLIC_SELECTOR);
        cd.extend(abi_encode_two_bytes(&tx_bytes, &artifacts));
        cd
    }

    fn build_register_calldata(token: [u8; 32], public_asset: [u8; 20]) -> Vec<u8> {
        let mut cd = Vec::from(REGISTER_TOKEN_SELECTOR);
        cd.extend_from_slice(&token);
        cd.extend_from_slice(&[0u8; 12]); // left-pad address to 32 bytes
        cd.extend_from_slice(&public_asset);
        cd
    }

    // Simulate the C++ store bridge — a BTreeMap that stores values correctly
    static TEST_STORE: Mutex<Option<BTreeMap<Vec<u8>, Vec<u8>>>> = Mutex::new(None);

    unsafe extern "C" fn test_store_get(
        _ctx: *mut c_void,
        key: *const u8, key_len: usize,
        value_buf: *mut u8, value_buf_len: usize,
        value_len: *mut usize,
    ) -> i32 {
        let key_slice = unsafe { slice::from_raw_parts(key, key_len) };
        let store = TEST_STORE.lock().unwrap();
        match store.as_ref().unwrap().get(key_slice) {
            Some(val) => {
                let copy_len = val.len().min(value_buf_len);
                unsafe {
                    std::ptr::copy_nonoverlapping(val.as_ptr(), value_buf, copy_len);
                    *value_len = copy_len;
                }
                1
            }
            None => {
                unsafe { *value_len = 0; }
                0
            }
        }
    }

    unsafe extern "C" fn test_store_set(
        _ctx: *mut c_void,
        key: *const u8, key_len: usize,
        value: *const u8, value_len: usize,
    ) {
        let key_slice = unsafe { slice::from_raw_parts(key, key_len) };
        let val_slice = unsafe { slice::from_raw_parts(value, value_len) };
        let mut store = TEST_STORE.lock().unwrap();
        store.as_mut().unwrap().insert(key_slice.to_vec(), val_slice.to_vec());
    }

    fn call_tinyvm_apply(sender: [u8; 20], value: u64, calldata: &[u8]) -> (bool, u128, String) {
        call_tinyvm_apply_with_logs(sender, value, calldata).0
    }

    fn call_tinyvm_apply_with_logs(sender: [u8; 20], value: u64, calldata: &[u8]) -> ((bool, u128, String), Vec<u8>) {
        let mut result = TinyVmApplyResult {
            escrow_refund: 0,
            token: [0; 32],
            owner: [0; 20],
            success: 0,
        };
        let mut error_buf = vec![0u8; 256];
        let mut logs_buf = vec![0u8; 4096];
        let mut logs_written: usize = 0;

        let rc = unsafe {
            tinyvm_apply(
                sender.as_ptr(), sender.len(),
                value, 0, // tx_value_lo, tx_value_hi
                calldata.as_ptr(), calldata.len(),
                std::ptr::null_mut(),
                test_store_get,
                test_store_set,
                &mut result,
                logs_buf.as_mut_ptr(), logs_buf.len(), &mut logs_written,
                error_buf.as_mut_ptr(), error_buf.len(),
            )
        };

        let error_msg = if rc != 1 {
            let nul = error_buf.iter().position(|&b| b == 0).unwrap_or(error_buf.len());
            String::from_utf8_lossy(&error_buf[..nul]).to_string()
        } else {
            String::new()
        };

        logs_buf.truncate(logs_written);
        ((result.success == 1, result.escrow_refund, error_msg), logs_buf)
    }

    /// Full result including owner and token fields.
    fn call_tinyvm_apply_full(sender: [u8; 20], value: u64, calldata: &[u8]) -> TinyVmApplyResult {
        let mut result = TinyVmApplyResult {
            escrow_refund: 0,
            token: [0; 32],
            owner: [0; 20],
            success: 0,
        };
        let mut error_buf = vec![0u8; 256];
        let mut logs_buf = vec![0u8; 4096];
        let mut logs_written: usize = 0;
        unsafe {
            tinyvm_apply(
                sender.as_ptr(), sender.len(),
                value, 0,
                calldata.as_ptr(), calldata.len(),
                std::ptr::null_mut(),
                test_store_get,
                test_store_set,
                &mut result,
                logs_buf.as_mut_ptr(), logs_buf.len(), &mut logs_written,
                error_buf.as_mut_ptr(), error_buf.len(),
            );
        }
        result
    }

    fn call_tinyvm_gas(calldata: &[u8]) -> u64 {
        unsafe { tinyvm_gas_cost(calldata.as_ptr(), calldata.len()) }
    }

    #[test]
    fn ffi_full_flow_via_abi_calldata() {
        // Initialize the test store
        *TEST_STORE.lock().unwrap() = Some(BTreeMap::new());

        let cfg = CryptoConfig::default();
        let token = [0x7au8; 32];
        let public_asset = native_mon_public_asset();
        let alice: [u8; 20] = [0xa1; 20];
        let bob: [u8; 20] = [0xb2; 20];

        // 1. registerToken
        let cd = build_register_calldata(token, public_asset);
        assert!(call_tinyvm_gas(&cd) > 0, "gas_cost should be >0 for registerToken");
        let (ok, escrow, err) = call_tinyvm_apply(alice, 0, &cd);
        assert!(ok, "registerToken failed: {err}");
        assert_eq!(escrow, 0, "registerToken escrow_refund should be 0");

        // 2. Shield Alice (90 wei)
        let alice_local = new_empty_local_account(&cfg, alice, token);
        let (shield_bundle, alice_after) = prove_shield_public(&cfg, &alice_local, 90).unwrap();
        let cd = build_shield_calldata(&shield_bundle);
        assert!(call_tinyvm_gas(&cd) > 0, "gas_cost should be >0 for shield");
        let (ok, escrow, err) = call_tinyvm_apply(alice, 90, &cd);
        assert!(ok, "shield alice failed: {err}");
        assert_eq!(escrow, 0, "shield: escrow_refund is 0 (msg.value handles it)");

        // 3. Shield Bob (7 wei)
        let bob_local = new_empty_local_account(&cfg, bob, token);
        let (shield_bundle, bob_after) = prove_shield_public(&cfg, &bob_local, 7).unwrap();
        let cd = build_shield_calldata(&shield_bundle);
        let (ok, escrow, err) = call_tinyvm_apply(bob, 7, &cd);
        assert!(ok, "shield bob failed: {err}");
        assert_eq!(escrow, 0, "shield: escrow_refund is 0 (msg.value handles it)");

        // 4. Transfer Alice -> Bob (30)
        let mut rng = rand::thread_rng();
        let (_, auditor_pub) = generate_auditor_keypair(&mut rng);
        let (transfer_call, _alice_after2) = prove_transfer_with_sidecars(
            &cfg, &alice_after, &bob_after, 30, Some(auditor_pub), &mut rng,
        ).unwrap();
        let cd = build_transfer_calldata(&transfer_call);
        assert!(call_tinyvm_gas(&cd) > 0, "gas_cost should be >0 for transfer");
        let (ok, escrow, err) = call_tinyvm_apply(alice, 0, &cd);
        assert!(ok, "transfer failed: {err}");
        assert_eq!(escrow, 0, "transfer escrow_refund should be 0");

        // 5. Unshield Bob (5 wei)
        let bob_after_transfer = apply_encrypted_recipient_memo(
            &cfg, &bob_after,
            &AccountState {
                owner: bob, token, version: 2,
                commitment: transfer_call.bundle.public.recipient_new_commitment,
            },
            transfer_call.sidecars.recipient_encrypted_memo.as_ref().unwrap(),
        ).unwrap();
        let (unshield_bundle, _) = prove_unshield_public(&cfg, &bob_after_transfer, 5).unwrap();
        let cd = build_unshield_calldata(&unshield_bundle);
        let (ok, escrow, err) = call_tinyvm_apply(bob, 0, &cd);
        assert!(ok, "unshield failed: {err}");
        assert_eq!(escrow, 5, "unshield: escrow_refund is the amount to return");

        // Cleanup
        *TEST_STORE.lock().unwrap() = None;
    }

    /// Verify TinyVmApplyResult struct layout matches the C header exactly.
    /// A mismatch means Rust writes success=1 at one offset but C++ reads
    /// it at another — causing silent reverts on every precompile call.
    #[test]
    fn ffi_struct_layout_matches_c() {
        use std::mem;

        // C header layout (tinyvm_ffi.h):
        //   unsigned __int128 escrow_refund; // offset 0, size 16
        //   uint8_t token[32];              // offset 16, size 32
        //   uint8_t owner[20];              // offset 48, size 20
        //   uint8_t success;                // offset 68, size 1
        //   padding to 16-byte alignment    // 69→80
        //   total: 80 bytes

        assert_eq!(mem::size_of::<TinyVmApplyResult>(), 80,
            "struct size must be 80 bytes to match C layout");

        let r = TinyVmApplyResult {
            escrow_refund: 0xDDEEFF00_11223344_55667788_99AABBCC_u128,
            token: [0xBB; 32],
            owner: [0xCC; 20],
            success: 0xAA,
        };

        let ptr = &r as *const TinyVmApplyResult as *const u8;
        unsafe {
            // escrow_refund at offset 0
            let refund_ptr = ptr as *const u128;
            assert_eq!(*refund_ptr, 0xDDEEFF00_11223344_55667788_99AABBCC_u128,
                "escrow_refund at offset 0");
            // token at offset 16
            assert_eq!(*ptr.add(16), 0xBB, "token starts at offset 16");
            // owner at offset 48
            assert_eq!(*ptr.add(48), 0xCC, "owner starts at offset 48");
            // success at offset 68
            assert_eq!(*ptr.add(68), 0xAA, "success at offset 68");
        }
    }

    #[test]
    fn ffi_normalize_abi_shield_round_trips() {
        let cfg = CryptoConfig::default();
        let alice: [u8; 20] = [0xa1; 20];
        let token = [0x7au8; 32];
        let local = new_empty_local_account(&cfg, alice, token);
        let (bundle, _) = prove_shield_public(&cfg, &local, 50).unwrap();
        let cd = build_shield_calldata(&bundle);

        // Verify ABI calldata normalizes to valid TVM2 envelope
        let normalized = normalize_input(&cd).expect("normalize should succeed");
        assert!(normalized.starts_with(&TINYVM_CALL_MAGIC), "normalized must have TVM2 magic");

        let decoded = tiny_privacy_vm_runtime::decode_tinyvm_call(&normalized).unwrap();
        assert_eq!(decoded.backend_id, CONFIDENTIAL_BACKEND_ID);
        assert_eq!(decoded.operation, TinyVmOperation::Shield);
    }

    #[test]
    fn ffi_shield_transfer_unshield_full_flow() {
        *TEST_STORE.lock().unwrap() = Some(BTreeMap::new());
        let cfg = CryptoConfig::default();
        let token = sample_token();
        let public_asset = native_mon_public_asset();
        let alice: [u8; 20] = [0xa1; 20];
        let bob: [u8; 20] = [0xb2; 20];
        let vault: [u8; 20] = [0xcc; 20]; // compliance vault

        // 1. Register
        let cd = build_register_calldata(token, public_asset);
        let (ok, _, err) = call_tinyvm_apply(alice, 0, &cd);
        assert!(ok, "register: {err}");

        // 2. Shield Alice 10 MON (10e18 wei)
        let alice_local = new_empty_local_account(&cfg, alice, token);
        let (shield_bundle, alice_after) = prove_shield_public(&cfg, &alice_local, 10_000_000_000_000_000_000).unwrap();
        let cd = build_shield_calldata(&shield_bundle);
        let (ok, refund, err) = call_tinyvm_apply(alice, 10_000_000_000_000_000_000u64, &cd);
        assert!(ok, "shield 10 MON: {err}");
        assert_eq!(refund, 0);

        // 3. Shield Bob 5 MON
        let bob_local = new_empty_local_account(&cfg, bob, token);
        let (shield_bob, bob_after) = prove_shield_public(&cfg, &bob_local, 5_000_000_000_000_000_000).unwrap();
        let cd = build_shield_calldata(&shield_bob);
        let (ok, _, err) = call_tinyvm_apply(bob, 5_000_000_000_000_000_000u64, &cd);
        assert!(ok, "shield bob: {err}");

        // 4. Transfer Alice→Bob 3 MON via vault (different sender)
        let mut rng = rand::thread_rng();
        let (transfer_call, alice_after2) = prove_transfer_with_sidecars(
            &cfg, &alice_after, &bob_after, 3_000_000_000_000_000_000, None, &mut rng,
        ).unwrap();
        assert_eq!(alice_after2.private.balance, 7_000_000_000_000_000_000);
        let cd = build_transfer_calldata(&transfer_call);
        let (ok, refund, err) = call_tinyvm_apply(vault, 0, &cd); // vault submits
        assert!(ok, "transfer via vault: {err}");
        assert_eq!(refund, 0);

        // 5. Unshield Alice 2 MON
        let (unshield_bundle, alice_after3) = prove_unshield_public(&cfg, &alice_after2, 2_000_000_000_000_000_000).unwrap();
        assert_eq!(alice_after3.private.balance, 5_000_000_000_000_000_000);
        let cd = build_unshield_calldata(&unshield_bundle);
        let (ok, refund, err) = call_tinyvm_apply(alice, 0, &cd);
        assert!(ok, "unshield 2 MON: {err}");
        assert_eq!(refund, 2_000_000_000_000_000_000u128);

        *TEST_STORE.lock().unwrap() = None;
    }

    /// Helper to parse the serialized log buffer.
    fn parse_logs(buf: &[u8]) -> Vec<(Vec<[u8; 32]>, Vec<u8>)> {
        let mut pos = 0;
        let num_logs = u32::from_le_bytes(buf[pos..pos+4].try_into().unwrap()) as usize;
        pos += 4;
        let mut logs = Vec::new();
        for _ in 0..num_logs {
            let num_topics = u32::from_le_bytes(buf[pos..pos+4].try_into().unwrap()) as usize;
            pos += 4;
            let mut topics = Vec::new();
            for _ in 0..num_topics {
                let mut t = [0u8; 32];
                t.copy_from_slice(&buf[pos..pos+32]);
                topics.push(t);
                pos += 32;
            }
            let data_len = u32::from_le_bytes(buf[pos..pos+4].try_into().unwrap()) as usize;
            pos += 4;
            let data = buf[pos..pos+data_len].to_vec();
            pos += data_len;
            logs.push((topics, data));
        }
        logs
    }

    #[test]
    fn ffi_logs_emitted_for_shield_transfer_unshield() {
        *TEST_STORE.lock().unwrap() = Some(BTreeMap::new());
        let cfg = CryptoConfig::default();
        let token = sample_token();
        let public_asset = native_mon_public_asset();
        let alice: [u8; 20] = [0xa1; 20];
        let bob: [u8; 20] = [0xb2; 20];

        // Register (no logs)
        let cd = build_register_calldata(token, public_asset);
        let ((ok, _, err), log_buf) = call_tinyvm_apply_with_logs(alice, 0, &cd);
        assert!(ok, "register: {err}");
        let logs = parse_logs(&log_buf);
        assert_eq!(logs.len(), 0, "register emits no logs");

        // Shield Alice
        let alice_local = new_empty_local_account(&cfg, alice, token);
        let (shield_bundle, alice_after) = prove_shield_public(&cfg, &alice_local, 90).unwrap();
        let cd = build_shield_calldata(&shield_bundle);
        let ((ok, _, err), log_buf) = call_tinyvm_apply_with_logs(alice, 90, &cd);
        assert!(ok, "shield: {err}");
        let logs = parse_logs(&log_buf);
        assert_eq!(logs.len(), 1, "shield emits 1 log");
        assert_eq!(logs[0].0.len(), 3, "shield log has 3 topics");

        // Shield Bob
        let bob_local = new_empty_local_account(&cfg, bob, token);
        let (shield_bundle, bob_after) = prove_shield_public(&cfg, &bob_local, 10).unwrap();
        let cd = build_shield_calldata(&shield_bundle);
        let (ok, _, err) = call_tinyvm_apply(bob, 10, &cd);
        assert!(ok, "shield bob: {err}");

        // Transfer Alice→Bob
        let mut rng = rand::thread_rng();
        let (_, auditor_pub) = generate_auditor_keypair(&mut rng);
        let (transfer_call, _) = prove_transfer_with_sidecars(
            &cfg, &alice_after, &bob_after, 30, Some(auditor_pub), &mut rng,
        ).unwrap();
        let cd = build_transfer_calldata(&transfer_call);
        let ((ok, _, err), log_buf) = call_tinyvm_apply_with_logs(alice, 0, &cd);
        assert!(ok, "transfer: {err}");
        let logs = parse_logs(&log_buf);
        assert_eq!(logs.len(), 1, "transfer emits 1 log");
        assert_eq!(logs[0].0.len(), 4, "transfer log has 4 topics (sig+from+to+token)");
        assert_eq!(logs[0].1.len(), 64, "transfer data = 2 × 32 bytes (sender+recip versions)");

        // Unshield Bob
        let bob_after_transfer = apply_encrypted_recipient_memo(
            &cfg, &bob_after,
            &AccountState {
                owner: bob, token, version: 2,
                commitment: transfer_call.bundle.public.recipient_new_commitment,
            },
            transfer_call.sidecars.recipient_encrypted_memo.as_ref().unwrap(),
        ).unwrap();
        let (unshield_bundle, _) = prove_unshield_public(&cfg, &bob_after_transfer, 5).unwrap();
        let cd = build_unshield_calldata(&unshield_bundle);
        let ((ok, _, err), log_buf) = call_tinyvm_apply_with_logs(bob, 0, &cd);
        assert!(ok, "unshield: {err}");
        let logs = parse_logs(&log_buf);
        assert_eq!(logs.len(), 1, "unshield emits 1 log");
        assert_eq!(logs[0].0.len(), 3, "unshield log has 3 topics");

        *TEST_STORE.lock().unwrap() = None;
    }

    /// Regression: FFI result must populate owner/token so the C++ side
    /// sends the escrow refund to the correct address, not address(0).
    #[test]
    fn ffi_unshield_result_has_correct_owner_and_token() {
        *TEST_STORE.lock().unwrap() = Some(BTreeMap::new());
        let cfg = CryptoConfig::default();
        let token = sample_token();
        let public_asset = native_mon_public_asset();
        let bob: [u8; 20] = [0xb2; 20];

        // Register + shield Bob
        let cd = build_register_calldata(token, public_asset);
        call_tinyvm_apply(bob, 0, &cd);
        let bob_local = new_empty_local_account(&cfg, bob, token);
        let (shield_bundle, bob_after) = prove_shield_public(&cfg, &bob_local, 100).unwrap();
        let cd = build_shield_calldata(&shield_bundle);
        let shield_result = call_tinyvm_apply_full(bob, 100, &cd);
        assert_eq!(shield_result.success, 1, "shield must succeed");
        assert_eq!(shield_result.escrow_refund, 0, "shield: no refund");
        assert_eq!(shield_result.owner, bob, "shield: owner must be bob");
        assert_eq!(shield_result.token, token, "shield: token must match");

        // Unshield 5
        let (unshield_bundle, _) = prove_unshield_public(&cfg, &bob_after, 5).unwrap();
        let cd = build_unshield_calldata(&unshield_bundle);
        let unshield_result = call_tinyvm_apply_full(bob, 0, &cd);
        assert_eq!(unshield_result.success, 1, "unshield must succeed");
        assert_eq!(unshield_result.escrow_refund, 5, "unshield: refund must be 5");
        assert_eq!(unshield_result.owner, bob, "unshield: owner must be bob, not address(0)");
        assert_eq!(unshield_result.token, token, "unshield: token must match");

        *TEST_STORE.lock().unwrap() = None;
    }
}
