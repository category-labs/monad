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

//! The witness guest proved with powdr's autoprecompiles: synthesised
//! precompiles for hot basic blocks, on top of the hand-written ones the guest
//! already uses for SHA-256, Keccak and the curve operations. Those stay —
//! powdr's `allowed_opcodes()` allowlist is what keeps their opcodes out of
//! autoprecompile candidates.
//!
//! ## Why this exists rather than powdr's own `powdr_openvm_riscv` CLI
//!
//! That CLI's `--input` and `--profile-input` are both `Option<u32>`, fed to
//! the guest through `StdIn::write` — a serialised integer. Its benchmark
//! guests take a scalar ("hash N times"); ours takes a multi-megabyte witness
//! blob and needs `write_bytes`. There is no flag for that, and the limit
//! applies to the profiling stage too, so no subcommand is usable for this
//! guest. The library underneath is what does the work: the APC pipeline is
//! called here exactly as their CLI calls it, so only the plumbing differs.
//!
//! Two other pieces of their CLI are bypassed. `compile_openvm` hardcodes an
//! empty target filter and so trips `find_unique_executable` on any package with
//! more than one binary — ours has two — so the `OriginalCompiledProgram` is
//! built here with the target named. And `powdr_openvm_riscv::prove` returns one
//! duration for app proving plus aggregation together, which cannot be compared
//! against a baseline split into core and recursion; `prove_phases` drives those
//! two halves instead. Their mock path is still used as-is — it never builds a
//! STARK, so there is nothing to split.

use std::path::PathBuf;
use std::time::Instant;

use clap::Parser;
use eyre::{Context, Result};
use monad_zkvm_openvm_script::{
    app_config, hex, prove_phases, report, report_peak_rss, stdin_from_bytes,
};
use openvm_sdk::config::{AggregationSystemParams, AppConfig};
use powdr_autoprecompiles::pgo::PgoType;
use powdr_autoprecompiles::{GenerateConfig, PgoConfig, SelectConfig};
use powdr_openvm::{PowdrSdkCpu, StagedPipeline};
use powdr_openvm_riscv::{
    CompiledProgram, OriginalCompiledProgram, RiscvISA, DEFAULT_DEGREE_BOUND,
};

#[derive(Parser)]
#[command(
    about = "Monad witness-execution guest — OpenVM host/prover with powdr autoprecompiles"
)]
struct Args {
    /// RLP-encoded execution witness to prove.
    #[arg(short, long)]
    input: PathBuf,

    /// Witness used to collect the execution profile that ranks basic blocks.
    /// Defaults to `--input`. Kept separate because it is what the APC set is
    /// derived from: profile once on a representative block, then prove many
    /// blocks against the same set. Changing it invalidates the cached
    /// generate/select/setup stages; changing `--input` does not.
    #[arg(long)]
    profile_input: Option<PathBuf>,

    /// The guest package to compile and transpile.
    #[arg(long, default_value = "..")]
    guest: PathBuf,

    /// Which binary in that package to build. The package also holds the
    /// precompile-test guest, so the target has to be named.
    #[arg(long, default_value = "monad-zkvm-openvm")]
    bin: String,

    /// Path to the VM extension config the guest is built against.
    #[arg(long, default_value = "../openvm.toml")]
    config: PathBuf,

    /// How many autoprecompiles to keep from the ranking.
    #[arg(long, default_value_t = 32)]
    autoprecompiles: usize,

    /// Skip this many top-ranked candidates before taking `--autoprecompiles`.
    #[arg(long, default_value_t = 0)]
    skip: usize,

    /// Candidate ranking strategy.
    #[arg(long, default_value = "cell")]
    pgo: PgoType,

    /// Persist stage artifacts here and reuse them on matching reruns. Worth
    /// setting: it is what makes an `--autoprecompiles` sweep cheap, since the
    /// generate stage is shared across selections.
    #[arg(long)]
    artifacts_dir: Option<PathBuf>,

    /// Per-segment memory budget, in GiB. OpenVM's default is 15.
    #[arg(long)]
    segment_memory_gib: Option<usize>,

    /// Report the segment count of the autoprecompiled program and stop.
    /// Cheap, and the number that predicts proving cost: core proving is
    /// linear in segments, so this compares directly against the baseline
    /// driver's `--mode segment` without paying for a full prove.
    #[arg(long, conflicts_with_all = ["mock", "recursion"])]
    segments: bool,

    /// Check constraints without producing a STARK. Much cheaper than proving
    /// and enough to tell whether the autoprecompiled program is sound. Note
    /// it says nothing about proving *speed* — it never builds a STARK.
    #[arg(long)]
    mock: bool,

    /// Fold the per-segment proofs into one via the recursion tree, then verify
    /// it. Off, this stops after core proving — the same split the baseline
    /// driver's `--prove` and `--prove-app` make.
    #[arg(long)]
    recursion: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let input = std::fs::read(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let profile_path = args.profile_input.as_ref().unwrap_or(&args.input);
    let profile_input = std::fs::read(profile_path)
        .with_context(|| format!("reading {}", profile_path.display()))?;

    println!("Monad witness-execution guest (OpenVM + powdr autoprecompiles)");
    println!("Input size:   {} bytes", input.len());
    println!("Profile input: {}", profile_path.display());
    println!("Autoprecompiles: {} (skip {})", args.autoprecompiles, args.skip);

    let started = Instant::now();
    let guest = compile_guest(&args)?;
    report("Compile + transpile", started);

    // The profiling stage runs the guest, so it needs the witness — which is
    // exactly what powdr's CLI cannot express. `PgoConfig::inputs` is opaque
    // bytes used only for cache keying, so the witness goes in there and the
    // closure below reads it back.
    let pgo_config = PgoConfig::new(args.pgo, None, profile_input);
    let select = SelectConfig::new(args.autoprecompiles as u64, args.skip as u64);
    let generate =
        GenerateConfig::new(DEFAULT_DEGREE_BOUND).with_select_defaults(args.pgo, select);

    let started = Instant::now();
    let program = StagedPipeline::new(guest, args.artifacts_dir.clone()).setup(
        &generate,
        &pgo_config,
        select,
        |guest, inputs: &[u8]| {
            powdr_openvm::execution_profile_from_guest(guest, stdin_from_bytes(inputs))
        },
        powdr_openvm::pipeline::make_default_empirical_constraints,
    );
    report("APC generate + select + setup", started);

    // Mock proving stays with powdr: it goes through their `do_with_trace`,
    // which re-reads the program rather than driving an SDK prover, so there is
    // nothing here to share with the baseline — and nothing to time apart,
    // since it never builds a STARK.
    if args.mock {
        let started = Instant::now();
        powdr_openvm_riscv::prove(&program, true, false, stdin_from_bytes(&input), None)
            .map_err(|e| eyre::eyre!("powdr mock prove failed: {e}"))?;
        report("Mock prove", started);
        report_peak_rss();
        return Ok(());
    }

    let sdk = powdr_sdk(&args, &program)?;

    // Execute before proving, as the baseline driver does and for the same
    // reason: the output is the post-state root, so seeing it first is what
    // says the autoprecompiled program still computes the right answer, and a
    // guest that halts non-zero is better caught before an hour of proving.
    // The segment count comes free with metering, and is the number the
    // autoprecompile effect shows up in first.
    let started = Instant::now();
    let (output, segments) = sdk.execute_metered(program.exe.clone(), stdin_from_bytes(&input))?;
    report("Metered execute", started);
    println!("Segments:     {}", segments.len());
    println!("Output: 0x{}", hex(&output));

    if args.segments {
        report_peak_rss();
        return Ok(());
    }

    prove_phases(
        &sdk,
        program.exe.clone(),
        stdin_from_bytes(&input),
        args.recursion,
    )?;
    report_peak_rss();

    Ok(())
}

/// The SDK for the autoprecompiled program, configured the way the baseline
/// driver configures its own.
///
/// This is built here rather than taken from `powdr_openvm_riscv::prove`, which
/// builds an equivalent one internally but exposes neither it nor the phase
/// boundaries inside — its recursion path is a single `StarkProver::prove` call,
/// so core and recursion come back as one number. Holding the SDK here is what
/// lets `prove_phases` split them, and `PowdrSdkCpu` being a plain `GenericSdk`
/// alias over powdr's specialised VM builder is what lets the baseline driver
/// share that code.
fn powdr_sdk(args: &Args, program: &CompiledProgram<RiscvISA>) -> Result<PowdrSdkCpu<RiscvISA>> {
    // The STARK system params come from the same `openvm.toml` read the
    // baseline driver uses, which is what makes the two sets of numbers
    // comparable by construction rather than by two independently built copies
    // happening to agree. That file names no `[system_params]`, so this is
    // `AppConfig`'s serde default — `app_params_with_100_bits_security(
    // MAX_APP_LOG_STACKED_HEIGHT)`, exactly what openvm-sdk itself applies, and
    // exactly what powdr's own path applies too.
    let system_params = app_config(&args.config, args.segment_memory_gib)?.system_params;
    let config = AppConfig::new(program.vm_config.clone(), system_params);
    Ok(PowdrSdkCpu::<RiscvISA>::new(
        config,
        AggregationSystemParams::default(),
    )?)
}

/// Compile and transpile the guest, then wrap it the way powdr's pipeline
/// expects. This mirrors `powdr_openvm_riscv::compile_openvm`, with two
/// changes: the target filter names our binary, and the VM config comes from
/// the same `openvm.toml` reader the baseline driver uses so both drivers agree
/// on `num_public_values` and the segment budget.
fn compile_guest(args: &Args) -> Result<OriginalCompiledProgram<'static, RiscvISA>> {
    use openvm_build::TargetFilter;
    use openvm_sdk_config::TranspilerConfig;
    use powdr_openvm::extraction_utils::OriginalVmConfig;
    use powdr_openvm_riscv::{build_elf_path, ExtendedVmConfig, GuestOptions};
    use powdr_openvm_riscv_hints_circuit::HintsExtension;
    use powdr_openvm_riscv_hints_transpiler::HintsTranspilerExtension;

    // `--emit-relocs` is what leaves the labels powdr needs to recover basic
    // block boundaries from the linked ELF.
    let guest_opts =
        GuestOptions::default().with_rustc_flags(vec!["-C", "link-arg=--emit-relocs"]);
    let target_filter = Some(TargetFilter {
        name: args.bin.clone(),
        kind: "bin".to_string(),
    });

    let app_config = app_config(&args.config, args.segment_memory_gib)?;
    let transpiler = app_config
        .app_vm_config
        .transpiler()
        .with_extension(HintsTranspilerExtension {});
    let sdk = openvm_sdk::Sdk::builder()
        .app_config(app_config)
        .agg_params(AggregationSystemParams::default())
        .transpiler(transpiler)
        .build_without_transpiler()?;

    let elf = sdk.build(guest_opts.clone(), &args.guest, &target_filter, None)?;
    let exe = sdk.convert_to_exe(elf)?;
    let elf_path = build_elf_path(guest_opts, &args.guest, &target_filter)?;
    let linked = powdr_riscv_elf::load_elf(&elf_path);

    let vm_config = ExtendedVmConfig {
        sdk: sdk.app_config().app_vm_config.clone(),
        hints: HintsExtension,
    };
    Ok(OriginalCompiledProgram::new(
        exe,
        OriginalVmConfig::new(vm_config),
        linked,
    ))
}
