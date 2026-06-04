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

// The guest ELF is produced by build.rs (C++ guest archive + program/main.c
// linked against the vendored SP1 SDK) and its path exported as GUEST_ELF.
const ELF_BYTES: &[u8] = include_bytes!(env!("GUEST_ELF"));
const MONAD_ELF: Elf = Elf::Static(ELF_BYTES);

#[derive(Parser)]
#[command(about = "Monad witness-execution guest — SP1 host/prover")]
struct Args {
    /// Path to the RLP-encoded execution witness binary.
    #[arg(short, long)]
    input: String,

    /// Run the SP1 prover after executing (generates and verifies a proof).
    #[arg(long)]
    prove: bool,
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

    // libzkevm's `read_input` (read_vec_raw) returns the raw input buffer, so
    // feed the witness bytes verbatim with write_slice. write_vec would prepend
    // length-prefix framing that read_input does not strip, corrupting the RLP.
    let mut stdin = SP1Stdin::new();
    stdin.write_slice(&input);

    let client = ProverClient::from_env().await;

    if args.prove {
        let pk = client.setup(MONAD_ELF).await.expect("setup failed");
        let proof = client.prove(&pk, stdin).await.expect("proving failed");
        client
            .verify(&proof, pk.verifying_key(), None)
            .expect("verification failed");
        println!("Proof generated and verified");
        println!("Output: {}", proof.public_values.raw());
    } else {
        let (output, report) = client
            .execute(MONAD_ELF, stdin)
            .await
            .expect("execution failed");
        println!("Cycles: {}", report.total_instruction_count());
        println!("Output: {}", output.raw());
    }
}
