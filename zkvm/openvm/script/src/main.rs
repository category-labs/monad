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

//! Host driver for the OpenVM guest, the counterpart of `zkvm/sp1/script`.
//!
//! `cargo openvm run` already executes a transpiled guest, so the reason this
//! exists is the things the CLI cannot do: frame a witness the way the guest's
//! `read_input` expects, raise `num_public_values` (which has no `openvm.toml`
//! representation — see the README's constraints section), and prove.
//!
//! Unlike the SP1 driver this does not build the guest. OpenVM's guest build
//! is a transpilation step owned by `cargo openvm build`, so the `.vmexe` is an
//! input here rather than something `build.rs` produces.

use std::path::PathBuf;
use std::sync::Arc;

use clap::{Parser, ValueEnum};
use eyre::{Context, Result};
use monad_zkvm_openvm_script::{
    app_config, hex, prove_phases, report_peak_rss, stdin_from_bytes,
};
use openvm_sdk::config::AggregationSystemParams;
use openvm_sdk::fs::read_object_from_file;
use openvm_sdk::openvm_circuit::arch::instructions::exe::VmExe;
use openvm_sdk::{Sdk, F};

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
enum Mode {
    /// Execute only.
    Pure,
    /// Execute and report trace-cell cost, the proxy for proving work.
    Meter,
    /// Execute and report how many segments proving would split into.
    Segment,
}

#[derive(Parser)]
#[command(about = "Monad witness-execution guest — OpenVM host/prover")]
struct Args {
    /// Path to the input binary: an RLP-encoded execution witness, or a
    /// precompile golden-vector blob when running the test guest.
    #[arg(short, long)]
    input: PathBuf,

    /// Path to the transpiled guest, as produced by `cargo openvm build`.
    #[arg(long, default_value = "../openvm/release/monad-zkvm-openvm.vmexe")]
    exe: PathBuf,

    /// Path to the VM extension config the guest was built against.
    #[arg(long, default_value = "../openvm.toml")]
    config: PathBuf,

    #[arg(long, value_enum, default_value = "pure")]
    mode: Mode,

    /// Per-segment memory budget, in GiB. This is the knob that trades peak
    /// prover memory against segment count: a smaller budget closes segments
    /// sooner, so each proof is cheaper but there are more of them to
    /// aggregate. OpenVM's default is 15 GiB. It is `serde(skip)` in
    /// `SystemConfig`, so it cannot come from `openvm.toml` and has to be set
    /// here.
    #[arg(long)]
    segment_memory_gib: Option<usize>,

    /// Generate and verify an aggregated STARK proof.
    #[arg(long)]
    prove: bool,

    /// Generate only the app-level continuation proof, skipping STARK
    /// aggregation.
    #[arg(long, conflicts_with = "prove")]
    prove_app: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let input = std::fs::read(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    // Shared rather than owned: the witness guest is a ~27 MB executable and
    // `--prove` hands it to a second SDK call, so cloning it would be a
    // needless deep copy.
    let exe: Arc<VmExe<F>> = Arc::new(
        read_object_from_file(&args.exe)
            .map_err(|e| eyre::eyre!("reading {}: {e}", args.exe.display()))?,
    );
    let sdk = Sdk::new(
        app_config(&args.config, args.segment_memory_gib)?,
        AggregationSystemParams::default(),
    )?;

    let stdin = stdin_from_bytes(&input);

    println!("Monad witness-execution guest (OpenVM)");
    println!("Input size: {} bytes", input.len());

    let output = match args.mode {
        Mode::Pure => sdk.execute(exe.clone(), stdin.clone())?,
        Mode::Meter => {
            let (output, (cost, instret)) =
                sdk.execute_metered_cost(exe.clone(), stdin.clone())?;
            println!("Instructions: {instret}");
            println!("Trace cells:  {cost}");
            output
        }
        Mode::Segment => {
            let (output, segments) = sdk.execute_metered(exe.clone(), stdin.clone())?;
            let instret: u64 = segments.iter().map(|s| s.num_insns).sum();
            println!("Instructions: {instret}");
            println!("Segments:     {}", segments.len());
            output
        }
    };
    println!("Output: 0x{}", hex(&output));

    // Proving runs after the execution above, which repeats the run: proving
    // takes long enough that seeing the committed output first is worth one
    // extra interpreted pass, and a guest that halts non-zero is better caught
    // before the prover starts.
    if args.prove || args.prove_app {
        prove_phases(&sdk, exe, stdin, args.prove)?;
    }
    report_peak_rss();
    Ok(())
}

