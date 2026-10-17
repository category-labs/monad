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

use clap::Parser;
use sp1_sdk::{utils, Elf, Prover, ProverClient, ProvingKey, SP1Stdin};

// build.rs exports the ELF path for the witness guest, or the precompile
// test guest when the `precompile-test` feature is enabled.
const ELF_BYTES: &[u8] = include_bytes!(env!("MONAD_ELF"));
const MONAD_ELF: Elf = Elf::Static(ELF_BYTES);

#[derive(Parser)]
#[command(about = "Monad witness-execution guest — SP1 host/prover")]
struct Args {
    /// Input file: an RLP execution witness
    #[arg(short, long)]
    input: String,

    /// Generate and verify a proof instead of only executing the guest.
    #[arg(long)]
    prove: bool,

    /// Report the instruction count during execution (ignored with --prove).
    /// Enables additional gas-estimation work.
    #[arg(long)]
    cycles: bool,
}

#[tokio::main]
async fn main() {
    utils::setup_logger();
    let args = Args::parse();

    let input = std::fs::read(&args.input).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", args.input, e);
        std::process::exit(1);
    });

    println!("Monad witness-execution guest (SP1)");
    println!("Witness size: {} bytes", input.len());

    // libzkevm's read_input exposes only the first input chunk, so send the
    // entire file as one raw chunk without additional serialization.
    let mut stdin = SP1Stdin::new();
    stdin.write_slice(&input);

    if args.prove {
        let client = ProverClient::from_env().await;
        let pk = client.setup(MONAD_ELF).await.expect("setup failed");
        let proof = client.prove(&pk, stdin).await.expect("proving failed");
        client
            .verify(&proof, pk.verifying_key(), None)
            .expect("verification failed");
        println!("Proof generated and verified");
        println!("Output: {}", proof.public_values.raw());
    } else {
        // Execution only needs the light client, avoiding prover initialization.
        let client = ProverClient::builder().light().build().await;
        let (output, report) = client
            .execute(MONAD_ELF, stdin)
            .calculate_gas(args.cycles)
            .await
            .expect("execution failed");
        if args.cycles {
            println!("Cycles: {}", report.total_instruction_count());
        }
        println!("Output: {}", output.raw());
    }
}
