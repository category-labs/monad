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

//! Shared by both host drivers — the plain-SDK one in `main.rs` and the
//! autoprecompile one in `bin/powdr.rs`. They report through the same helpers
//! on purpose: the whole point of the second driver is a number comparable
//! with the first, so the config, the input framing and the timing all have to
//! come from one place.

use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

use eyre::{Context, Result};
use openvm_sdk::config::AppConfig;
use openvm_sdk::openvm_circuit::arch::instructions::exe::VmExe;
use openvm_sdk::openvm_circuit::arch::{
    Executor, MeteredExecutor, PreflightExecutor, VmBuilder, VmExecutionConfig,
};
use openvm_sdk::{DefaultStarkEngine, GenericSdk, StdIn, F};
use openvm_sdk_config::SdkVmConfig;

/// Bytes of public-value address space to give the guest.
///
/// Must be 8 x a power of two. The witness guest commits a 32-byte post-state
/// root and would fit the 32-byte default, but the precompile-test guest's
/// failure log runs to 244 bytes, and a config mismatch between the two would
/// mean two proving keys for no real benefit.
pub const NUM_PUBLIC_VALUES: usize = 256;

/// Build the VM config from the same `openvm.toml` the guest was built from.
///
/// Reading the file rather than calling `SdkVmConfig::standard()` keeps one
/// source of truth: that file also generates the guest's `openvm_init.rs`, and
/// the moduli and curve *order* in it fixes the setup indices compiled into the
/// guest. A config that agreed with `standard()` but not with the file would
/// still mismatch the binary.
pub fn app_config(
    path: &Path,
    segment_memory_gib: Option<usize>,
) -> Result<AppConfig<SdkVmConfig>> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("reading {}", path.display()))?;
    let mut config: AppConfig<SdkVmConfig> = toml::from_str(&text)
        .with_context(|| format!("parsing {}", path.display()))?;
    config.app_vm_config.system.config = config
        .app_vm_config
        .system
        .config
        .clone()
        .with_public_values(NUM_PUBLIC_VALUES);
    if let Some(gib) = segment_memory_gib {
        config
            .app_vm_config
            .system
            .config
            .segmentation_config
            .limits
            .max_memory = gib << 30;
    }
    Ok(config)
}

/// Frame a witness the way the guest's `read_input` expects.
///
/// It is idempotent and exposes only the first input record, so the payload
/// has to be exactly one `write_bytes` vector — the same single-buffer framing
/// SP1 gets from `write_slice`. Note this is `write_bytes`, not `write`: the
/// latter would serialise the slice with a length prefix that `read_vec` does
/// not strip. That distinction is why the autoprecompile driver cannot reuse
/// powdr's own CLI, whose `--input` is an `Option<u32>` fed through `write`.
pub fn stdin_from_bytes(input: &[u8]) -> StdIn {
    let mut stdin = StdIn::default();
    stdin.write_bytes(input);
    stdin
}

/// Peak resident set size in bytes, from `VmHWM`. Proving is memory-bound well
/// before it is CPU-bound, so this is the number that decides whether a block
/// fits on a given machine.
///
/// `VmHWM` is a process-wide high-water mark, which is why this is reported once
/// per run and not per phase: past the largest phase it can only repeat itself,
/// so a per-phase column of it would read as a measurement while carrying a
/// single number. Use `VmRSS` instead if a phase-by-phase profile is ever
/// wanted — but note that samples the instant it is read, not that phase's peak.
pub fn peak_rss() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
    let kb: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(kb * 1024)
}

pub fn report(phase: &str, started: Instant) {
    println!("{phase}: {:.1} s", started.elapsed().as_secs_f64());
}

/// Print the run's peak RSS. Call once, after the last phase.
pub fn report_peak_rss() {
    if let Some(bytes) = peak_rss() {
        println!("Peak RSS: {:.1} GiB", bytes as f64 / (1u64 << 30) as f64);
    }
}

/// Prove the guest, timing the phases apart, then verify.
///
/// This drives the two halves of `Sdk::prove` by hand rather than calling it, so
/// core proving and recursion can be timed separately — worth the duplication
/// because core proving dominates, and a change that moves only the total says
/// less than one that says which half moved. It reproduces `prove`'s
/// no-deferral path exactly: no deferral inputs are ever passed, so the branches
/// it guards on `def_inputs` and `hook_commit` are dead here. The one thing that
/// has to stay in step with upstream is the extra internal-recursive wrap it
/// applies to shrink the final proof.
///
/// `recursion` off stops after the per-segment proofs — one proof per segment,
/// so the total size grows with runtime, but it isolates the cost of proving the
/// block from the cost of folding those proofs together.
///
/// Generic over the VM builder because that is what makes the autoprecompile
/// numbers comparable: `PowdrSdkCpu` is a `GenericSdk` over powdr's specialised
/// builder, so both drivers get these phase boundaries from one definition
/// rather than from two copies that happen to agree today. The engine is not
/// generic — `DefaultStarkEngine` follows openvm-sdk's own `cuda` feature, which
/// is also the only thing that could make it disagree with powdr's `PowdrSdkCpu`
/// (they have a `PowdrSdkGpu` for that case). Neither is built with `cuda` here,
/// and a mismatch would be a compile error at the call site rather than a
/// silently different measurement.
pub fn prove_phases<VB>(
    sdk: &GenericSdk<DefaultStarkEngine, VB>,
    exe: Arc<VmExe<F>>,
    stdin: StdIn,
    recursion: bool,
) -> Result<()>
where
    VB: VmBuilder<DefaultStarkEngine> + Clone,
    <VB::VmConfig as VmExecutionConfig<F>>::Executor:
        Executor<F> + MeteredExecutor<F> + PreflightExecutor<F, VB::RecordArena>,
{
    // Keygen sits outside the end-to-end span below: it depends on the program
    // and the config, not on the block, so it is amortised over every block
    // proved against the same executable rather than charged to one of them.
    let started = Instant::now();
    let mut prover = sdk.prover(exe)?;
    report("Keygen", started);

    let end_to_end = Instant::now();
    let started = Instant::now();
    let continuation = prover.app_prover.prove(stdin)?;
    let segments = continuation.per_segment.len();
    report("Core proof", started);
    println!("Segments proved: {segments}");

    if !recursion {
        return Ok(());
    }

    let started = Instant::now();
    let (mut proof, mut metadata) = prover.agg_prover.prove_vm(continuation)?;
    proof = prover.agg_prover.wrap_proof(proof, &mut metadata)?;
    report("Recursion", started);
    report("End to end", end_to_end);

    // `verify_proof` takes no `self`: verification depends only on the
    // aggregation verifying key and the baseline commitment to the app
    // executable, never on the app config held by this Sdk.
    let started = Instant::now();
    let baseline = prover.generate_baseline();
    let agg_vk = sdk.agg_vk();
    GenericSdk::<DefaultStarkEngine, VB>::verify_proof(
        agg_vk.as_ref().clone(),
        baseline,
        &proof,
    )?;
    report("Verify", started);

    Ok(())
}

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
