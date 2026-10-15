//! Runs the Monad guest in Airbender's transpiler VM, as `cargo airbender run`
//! and `cargo airbender flamegraph` do, with a host that answers the guest's
//! oracle queries: quotients of 256-bit divisions, which the guest checks with
//! a multiply and a subtract on the bigint circuit instead of dividing, and
//! the secp256k1 field hints of ecrecover (quotients, inverses and square
//! roots, each checked with a multiplication).
//!
//! A query goes through the non-determinism CSR as a tag word naming it, then
//! the address of each operand. When the last address arrives the host reads
//! the operands from guest RAM and queues its answer, which the guest reads
//! back word by word. Every word the guest reads is recorded: the transcript
//! (`--transcript`) is an input file with which the stock `cargo airbender
//! prove` replays the run, since its source serves reads in order and ignores
//! writes that are not UART messages.
//!
//! usage: monad-airbender-runner run <app.bin> --input <hex> [--text-path <text>]
//!            [--cycles <n>] [--transcript <hex>]
//!        monad-airbender-runner flamegraph <app.bin> --input <hex>
//!            [--output <svg>] [--elf-path <elf>] [--sampling-rate <n>]

use airbender_host::raw::{NonDeterminismCSRSource, RamPeek};
use airbender_host::{FlamegraphConfig, TranspilerRunnerBuilder};
use num_bigint::BigUint;
use std::collections::VecDeque;
use std::path::PathBuf;

/// Query tags: "VDM" in the high bytes, the query in the low one.
const TAG_MASK: u32 = 0xffff_ff00;
const TAG: u32 = 0x4d44_5600;
/// (u, v): u / v, eight words.
const DIV: u32 = TAG | 1;
/// (lo, hi, d): (hi·2^256 + lo) / d, sixteen words, low half first.
const WIDE_DIV: u32 = TAG | 2;
/// secp256k1 field hints on one operand, read and answered in the guest's
/// representation, as ZKsync OS's oracle answers its RISC-V guest
/// (basic_system field_ops.rs): Montgomery words, x·2^256 mod m, any
/// representative below 2^256 in, the canonical one out.
/// The numerator and the denominator, adjacent: their quotient.
const SECP_DIVIDE: u32 = TAG | 0x10;
/// x: x^((p+1)/4), then a word that is 1 if x is not a square (the root is
/// then -x's).
const SECP_SQRT: u32 = TAG | 0x11;
/// x: 1/x.
const SECP_INVERT: u32 = TAG | 0x12;
/// s: 1/s modulo the group order.
const SECP_SCALAR_INVERT: u32 = TAG | 0x13;

const QUERIES: [(u32, &str); 6] = [
    (DIV, "div"),
    (WIDE_DIV, "wide_div"),
    (SECP_DIVIDE, "secp_divide"),
    (SECP_SQRT, "secp_sqrt"),
    (SECP_INVERT, "secp_invert"),
    (SECP_SCALAR_INVERT, "secp_scalar_invert"),
];

fn operand_count(tag: u32) -> usize {
    match tag {
        DIV => 2,
        WIDE_DIV => 3,
        SECP_DIVIDE | SECP_SQRT | SECP_INVERT | SECP_SCALAR_INVERT => 1,
        _ => 0,
    }
}

/// A prime field in the guest's Montgomery representation.
struct Field {
    m: BigUint,
    r: BigUint,
    r_inverse: BigUint,
}

impl Field {
    fn new(modulus_hex: &str) -> Self {
        let m = BigUint::parse_bytes(modulus_hex.as_bytes(), 16).unwrap();
        let r = (BigUint::from(1u32) << 256u32) % &m;
        let r_inverse = r.modinv(&m).unwrap();
        Self { m, r, r_inverse }
    }

    /// The element of the guest's words.
    fn element(&self, words: BigUint) -> BigUint {
        words % &self.m * &self.r_inverse % &self.m
    }

    /// The guest's words of an element.
    fn words(&self, x: &BigUint) -> BigUint {
        x * &self.r % &self.m
    }

    /// 1/x, and 0 for 0 (never asked: the guest's check would refuse it).
    fn inverse(&self, x: &BigUint) -> BigUint {
        x.modinv(&self.m).unwrap_or_default()
    }
}

/// The 256-bit little-endian number at `address` in guest RAM.
fn read_u256<R: RamPeek + ?Sized>(ram: &R, address: u32) -> BigUint {
    assert_eq!(address % 4, 0, "operand at {address:#x} is not word-aligned");
    let words: Vec<u32> = (0..8).map(|i| ram.peek_word(address + 4 * i)).collect();
    BigUint::from_slice(&words)
}

/// QuasiUART, as riscv_transpiler's QuasiUARTSourceState: 0xffffffff, then a
/// word count, a byte length and the words of the message.
#[derive(Default)]
struct Uart {
    message: Option<(Option<usize>, Option<usize>, Vec<u8>)>,
}

impl Uart {
    fn busy(&self) -> bool {
        self.message.is_some()
    }

    fn write(&mut self, value: u32) {
        let Some((words, len, buffer)) = &mut self.message else {
            if value == u32::MAX {
                self.message = Some((None, None, Vec::new()));
            }
            return;
        };
        let Some(remaining_words) = words else {
            *words = Some(value as usize);
            return;
        };
        let Some(remaining_len) = len else {
            *remaining_words -= 1;
            *len = Some(value as usize);
            return;
        };
        if *remaining_words > 0 {
            *remaining_words -= 1;
            let take = (*remaining_len).min(4);
            buffer.extend_from_slice(&value.to_le_bytes()[..take]);
            *remaining_len -= take;
        }
        if *remaining_words == 0 {
            println!("UART: `{}`", String::from_utf8_lossy(buffer));
            self.message = None;
        }
    }
}

struct Oracle {
    input: VecDeque<u32>,
    answers: VecDeque<u32>,
    query: Option<(u32, Vec<u32>)>,
    uart: Uart,
    transcript: Vec<u32>,
    /// Queries answered, by tag (QUERIES' order).
    counts: [u64; QUERIES.len()],
    /// `--corrupt <n>:<how>`: a wrong answer to the n-th query, to check
    /// that the guest refuses it.
    corrupt: Option<(u64, String)>,
    secp_p: Field,
    secp_n: Field,
}

impl Oracle {
    fn new(input: Vec<u32>) -> Self {
        Self {
            input: input.into(),
            answers: VecDeque::new(),
            query: None,
            uart: Uart::default(),
            transcript: Vec::new(),
            counts: [0; QUERIES.len()],
            corrupt: None,
            secp_p: Field::new("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"),
            secp_n: Field::new("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"),
        }
    }

    fn count(&self, tag: u32) -> u64 {
        QUERIES.iter().zip(&self.counts).find(|((t, _), _)| *t == tag).map_or(0, |(_, n)| *n)
    }

    fn write<R: RamPeek + ?Sized>(&mut self, ram: &R, value: u32) {
        if self.uart.busy() {
            self.uart.write(value);
        } else if let Some((_, addresses)) = &mut self.query {
            addresses.push(value);
            let (tag, addresses) = self.query.take().unwrap();
            if addresses.len() == operand_count(tag) {
                self.answer(ram, tag, &addresses);
            } else {
                self.query = Some((tag, addresses));
            }
        } else if value & TAG_MASK == TAG && operand_count(value) > 0 {
            self.query = Some((value, Vec::with_capacity(3)));
        } else {
            self.uart.write(value);
        }
    }

    fn answer<R: RamPeek + ?Sized>(&mut self, ram: &R, tag: u32, addresses: &[u32]) {
        assert!(self.answers.is_empty(), "query before the last answer was read");
        let index = QUERIES.iter().position(|(t, _)| *t == tag).unwrap();
        self.counts[index] += 1;
        // The answer: a value of `words` words, then for a square root its
        // flag. A zero divisor is never queried; it gets a zero, which fails
        // the guest's check.
        let (mut value, words, mut flag) = match tag {
            DIV => {
                let u = read_u256(ram, addresses[0]);
                let v = read_u256(ram, addresses[1]);
                (if v.bits() == 0 { v } else { u / v }, 8, None)
            }
            WIDE_DIV => {
                let lo = read_u256(ram, addresses[0]);
                let hi = read_u256(ram, addresses[1]);
                let d = read_u256(ram, addresses[2]);
                (if d.bits() == 0 { d } else { ((hi << 256u32) + lo) / d }, 16, None)
            }
            SECP_DIVIDE => {
                let f = &self.secp_p;
                let numerator = f.element(read_u256(ram, addresses[0]));
                let denominator = f.element(read_u256(ram, addresses[0] + 32));
                let quotient = numerator * f.inverse(&denominator) % &f.m;
                (f.words(&quotient), 8, None)
            }
            SECP_SQRT => {
                let f = &self.secp_p;
                let x = f.element(read_u256(ram, addresses[0]));
                let root = x.modpow(&((&f.m + 1u32) >> 2u32), &f.m);
                let not_square = &root * &root % &f.m != x;
                (f.words(&root), 8, Some(u32::from(not_square)))
            }
            SECP_INVERT => {
                let f = &self.secp_p;
                let x = f.element(read_u256(ram, addresses[0]));
                (f.words(&f.inverse(&x)), 8, None)
            }
            SECP_SCALAR_INVERT => {
                let f = &self.secp_n;
                let x = f.element(read_u256(ram, addresses[0]));
                (f.words(&f.inverse(&x)), 8, None)
            }
            _ => unreachable!(),
        };
        if let Some((n, how)) = &self.corrupt {
            if *n == self.counts.iter().sum::<u64>() {
                let top: BigUint = BigUint::from(1u32) << (32 * words - 1);
                let all: BigUint = (BigUint::from(1u32) << (32 * words)) - 1u32;
                match how.as_str() {
                    "inc" => value = (value + 1u32) & &all,
                    "dec" if value.bits() == 0 => value = all.clone(),
                    "dec" => value -= 1u32,
                    "flip" => value ^= top,
                    "zero" => value = BigUint::default(),
                    "flag" => flag = flag.map(|f| f ^ 1),
                    _ => panic!("--corrupt <n>:inc|dec|flip|zero|flag"),
                }
                eprintln!("corrupted query {n} ({how})");
            }
        }
        let mut digits = value.to_u32_digits();
        digits.resize(words, 0);
        self.answers.extend(digits);
        self.answers.extend(flag);
    }
}

/// The VM takes its source by value; this hands it the oracle and keeps the
/// oracle's transcript and counts for after the run.
struct Source<'a>(&'a mut Oracle);

/// Guest RAM handed over as a word slice.
struct Words<'a>(&'a [u32]);

impl RamPeek for Words<'_> {
    fn peek_word(&self, address: u32) -> u32 {
        self.0[(address / 4) as usize]
    }
}

impl NonDeterminismCSRSource for Source<'_> {
    fn read(&mut self) -> u32 {
        let oracle = &mut *self.0;
        let word = oracle
            .answers
            .pop_front()
            .or_else(|| oracle.input.pop_front())
            .expect("the guest read past its input");
        oracle.transcript.push(word);
        word
    }

    fn write_with_memory_access<R: RamPeek + ?Sized>(&mut self, ram: &R, value: u32) {
        self.0.write(ram, value);
    }

    fn write_with_memory_access_raw(&mut self, ram: &[u32], value: u32) {
        self.0.write(&Words(ram), value);
    }

    fn write_with_memory_access_dyn(&mut self, ram: &dyn RamPeek, value: u32) {
        self.0.write(ram, value);
    }
}

fn parse_hex_words(text: &str) -> Vec<u32> {
    let hex: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    let hex = hex.strip_prefix("0x").unwrap_or(&hex);
    assert!(hex.len() % 8 == 0, "input hex length must be a multiple of 8");
    hex.as_bytes()
        .chunks(8)
        .map(|chunk| u32::from_str_radix(std::str::from_utf8(chunk).unwrap(), 16).unwrap())
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = "usage: monad-airbender-runner run|flamegraph <app.bin> --input <hex> \
                 [--text-path <text>] [--cycles <n>] [--transcript <hex>] \
                 [--output <svg>] [--elf-path <elf>] [--sampling-rate <n>]";
    if args.len() < 3 || !matches!(args[1].as_str(), "run" | "flamegraph") {
        eprintln!("{usage}");
        std::process::exit(2);
    }
    let option = |name: &str| {
        args.iter()
            .position(|a| a == name)
            .map(|i| args.get(i + 1).unwrap_or_else(|| panic!("{name} needs a value")).clone())
    };
    let input_path = option("--input").unwrap_or_else(|| panic!("{usage}"));
    let input = parse_hex_words(&std::fs::read_to_string(&input_path).expect("read --input"));

    let mut builder = TranspilerRunnerBuilder::new(&args[2]);
    if let Some(text) = option("--text-path") {
        builder = builder.with_text_path(text);
    }
    if let Some(cycles) = option("--cycles") {
        builder = builder.with_cycles(cycles.parse().expect("--cycles"));
    }
    if args[1] == "flamegraph" {
        builder = builder.with_flamegraph(FlamegraphConfig {
            output: option("--output").unwrap_or_else(|| "flamegraph.svg".into()).into(),
            sampling_rate: option("--sampling-rate").map_or(100, |s| s.parse().expect("--sampling-rate")),
            inverse: false,
            elf_path: option("--elf-path").map(PathBuf::from),
        });
    }
    let runner = builder.build().expect("transpiler runner");

    let mut oracle = Oracle::new(input);
    oracle.corrupt = option("--corrupt").map(|c| {
        let (n, how) = c.split_once(':').expect("--corrupt <n>:<how>");
        (n.parse().expect("--corrupt <n>"), how.to_string())
    });
    let outcome = runner.run_with_source(Source(&mut oracle)).expect("transpiler execution");

    println!("  cycles: {}", outcome.cycles_executed);
    println!("  reached_end: {}", outcome.reached_end);
    println!("  final_pc: {:#x}", outcome.final_pc);
    let outputs: Vec<String> = outcome
        .receipt
        .output
        .iter()
        .enumerate()
        .map(|(i, v)| format!("x{}={}", i + 10, v))
        .collect();
    println!("  outputs: {}", outputs.join(" "));
    println!(
        "  queries: div={} wide_div={} words_read={} input_left={}",
        oracle.count(DIV),
        oracle.count(WIDE_DIV),
        oracle.transcript.len(),
        oracle.input.len()
    );
    let hints: Vec<String> = QUERIES[2..]
        .iter()
        .map(|(tag, name)| format!("{name}={}", oracle.count(*tag)))
        .collect();
    println!("  hints: {}", hints.join(" "));
    if let Some(path) = option("--transcript") {
        let hex: String = oracle.transcript.iter().map(|w| format!("{w:08x}")).collect();
        std::fs::write(&path, hex).expect("write --transcript");
        println!("  transcript: {path}");
    }
}
