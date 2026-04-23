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

//! CLI for inspecting and mutating monad triedb files.

use std::{path::PathBuf, process};

use clap::{Parser, Subcommand};
use futures::channel::oneshot;
use monad_triedb::{NibblesView, Triedb, TriedbRoHandle, TriedbRwHandle, UpsertEntry};

#[derive(Parser, Debug)]
#[command(
    name = "monad-triedb-cli",
    about = "Inspect and mutate monad triedb files"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

/// Source of the root that an upsert builds on top of.
#[derive(Debug, Clone, Copy)]
enum Base {
    Empty,
    Latest,
    Block(u64),
}

impl std::str::FromStr for Base {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "empty" => Ok(Self::Empty),
            "latest" => Ok(Self::Latest),
            other => other
                .parse::<u64>()
                .map(Self::Block)
                .map_err(|_| format!("expected `empty`, `latest`, or a block number; got {other}")),
        }
    }
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Print metadata about the triedb.
    Info {
        /// Path to the triedb file or directory.
        #[arg(long)]
        path: PathBuf,
    },
    /// Look up a single key and print its value as hex.
    Get {
        #[arg(long)]
        path: PathBuf,
        /// Key as hex digits, even length, no `0x` prefix.
        key: String,
        /// Block version to read from. Defaults to the latest finalized block.
        #[arg(long)]
        block: Option<u64>,
    },
    /// Traverse a subtrie and print every (key, value) pair as hex.
    Dump {
        #[arg(long)]
        path: PathBuf,
        /// Prefix as hex digits, even length, no `0x` prefix. Defaults to
        /// empty (full trie).
        #[arg(default_value = "")]
        prefix: String,
        #[arg(long)]
        block: Option<u64>,
    },
    /// Create a new empty triedb. Fails if the file already exists unless
    /// `--force` is passed.
    Create {
        #[arg(long)]
        path: PathBuf,
        /// Truncate an existing file at `path`.
        #[arg(long)]
        force: bool,
        /// File size to ftruncate the backing storage to, in GiB.
        #[arg(long, default_value_t = 4)]
        file_size_gb: i64,
        /// Enable compaction on writes.
        #[arg(long)]
        compaction: bool,
    },
    /// Write one or more (key, value) pairs at `--block`, then finalize
    /// that version.
    ///
    /// The positional `pairs` argument is `key:value[,key:value...]` where
    /// each key and value is a sequence of hex digits (no `0x` prefix).
    /// Keys must be byte-aligned (even-length hex) and non-empty. Values
    /// may be empty.
    Write {
        #[arg(long)]
        path: PathBuf,
        /// Block version to write at.
        #[arg(long)]
        block: u64,
        /// Root to build the new version on top of: `empty` (default),
        /// `latest` (current highest version in the DB), or a specific
        /// block number.
        #[arg(long, default_value = "empty")]
        base: Base,
        /// Comma-separated `key:value` pairs, hex-encoded.
        pairs: String,
        /// File size to ftruncate the backing storage to if the file does
        /// not yet exist. Ignored for existing files.
        #[arg(long, default_value_t = 4)]
        file_size_gb: i64,
        /// Enable compaction on writes.
        #[arg(long)]
        compaction: bool,
    },
}

const NODE_LRU_MAX_MEM: u64 = 64 << 20;

fn main() {
    let cli = Cli::parse();
    if let Err(err) = run(cli) {
        eprintln!("error: {err}");
        process::exit(1);
    }
}

fn run(cli: Cli) -> Result<(), String> {
    match cli.command {
        Command::Info { path } => cmd_info(&path),
        Command::Get { path, key, block } => cmd_get(&path, &key, block),
        Command::Dump {
            path,
            prefix,
            block,
        } => cmd_dump(&path, &prefix, block),
        Command::Create {
            path,
            force,
            file_size_gb,
            compaction,
        } => cmd_create(&path, force, file_size_gb, compaction),
        Command::Write {
            path,
            block,
            base,
            pairs,
            file_size_gb,
            compaction,
        } => cmd_write(&path, block, base, &pairs, file_size_gb, compaction),
    }
}

fn cmd_info(path: &std::path::Path) -> Result<(), String> {
    let handle = open_ro(path)?;
    println!("path:                      {}", path.display());
    println!(
        "earliest finalized:        {}",
        fmt_block(handle.earliest_finalized_block())
    );
    println!(
        "latest finalized:          {}",
        fmt_block(handle.latest_finalized_block())
    );
    println!(
        "latest verified:           {}",
        fmt_block(handle.latest_verified_block())
    );
    println!(
        "latest voted:              {}",
        fmt_block(handle.latest_voted_block())
    );
    println!(
        "latest voted block id:     {}",
        fmt_id(handle.latest_voted_block_id())
    );
    println!(
        "latest proposed:           {}",
        fmt_block(handle.latest_proposed_block())
    );
    println!(
        "latest proposed block id:  {}",
        fmt_id(handle.latest_proposed_block_id())
    );
    Ok(())
}

fn cmd_get(path: &std::path::Path, key_hex: &str, block: Option<u64>) -> Result<(), String> {
    let handle = open_ro(path)?;
    let block = resolve_block(&handle, block)?;
    let key_bytes = parse_hex(key_hex)?;
    let key = NibblesView::from_bytes(&key_bytes)
        .ok_or_else(|| format!("key too long: {} bytes", key_bytes.len()))?;

    match handle.find(key, block) {
        Some(value) => {
            println!("{}", hex::encode(value.bytes()));
            Ok(())
        }
        None => Err(format!("key {key_hex} not found at block {block}")),
    }
}

fn cmd_dump(path: &std::path::Path, prefix_hex: &str, block: Option<u64>) -> Result<(), String> {
    let mut handle = open_ro(path)?;
    let block = resolve_block(&handle, block)?;
    let prefix_bytes = parse_hex(prefix_hex)?;
    let prefix = NibblesView::from_bytes(&prefix_bytes)
        .ok_or_else(|| format!("prefix too long: {} bytes", prefix_bytes.len()))?;

    let (tx, mut rx) = oneshot::channel();
    handle.traverse_blocking(prefix, block, tx);

    // traverse_blocking fires the finished callback before returning, so
    // the sender has already completed.
    let entries = rx
        .try_recv()
        .map_err(|_| "traverse channel cancelled")?
        .ok_or("traverse channel produced no result")?
        .ok_or_else(|| format!("traverse failed at prefix {prefix_hex} block {block}"))?;

    for entry in &entries {
        println!("{}  {}", hex::encode(&entry.key), hex::encode(&entry.value));
    }
    eprintln!("{} entries", entries.len());
    Ok(())
}

fn cmd_create(
    path: &std::path::Path,
    force: bool,
    file_size_gb: i64,
    compaction: bool,
) -> Result<(), String> {
    if path.exists() && !force {
        return Err(format!(
            "{} already exists; pass --force to truncate",
            path.display()
        ));
    }
    let _ = TriedbRwHandle::create(path, NODE_LRU_MAX_MEM, file_size_gb, compaction)
        .map_err(|e| format!("failed to create {}: {e}", path.display()))?;
    println!("created empty triedb at {}", path.display());
    Ok(())
}

fn cmd_write(
    path: &std::path::Path,
    block: u64,
    base: Base,
    pairs_arg: &str,
    file_size_gb: i64,
    compaction: bool,
) -> Result<(), String> {
    let entries = parse_pairs(pairs_arg)?;

    let mut db = TriedbRwHandle::open_rw(path, NODE_LRU_MAX_MEM, file_size_gb, compaction)
        .map_err(|e| format!("failed to open {}: {e}", path.display()))?;

    match base {
        Base::Empty => {}
        Base::Latest => {
            let latest = db
                .latest_version()
                .ok_or("--base latest requested but the db has no existing version")?;
            let loaded = db.load_root(latest);
            if !loaded {
                return Err(format!(
                    "failed to load root for version {latest} (reported as latest)"
                ));
            }
        }
        Base::Block(version) => {
            if version >= block {
                return Err(format!(
                    "--base {version} must be strictly less than --block {block}"
                ));
            }
            let loaded = db.load_root(version);
            if !loaded {
                return Err(format!("version {version} is not present in the db"));
            }
        }
    }

    db.upsert(&entries, block);
    db.update_finalized_version(block);

    let base_desc = match base {
        Base::Empty => "empty".to_owned(),
        Base::Latest => "latest".to_owned(),
        Base::Block(v) => format!("block {v}"),
    };
    println!(
        "wrote {} key(s) at block {block} (base: {base_desc})",
        entries.len()
    );
    Ok(())
}

/// Parse a `key1:value1,key2:value2,...` argument into UpsertEntry values.
///
/// Rules, enforced explicitly:
/// - The argument must not be empty.
/// - Each comma-separated item must contain exactly one `:`.
/// - Keys must be non-empty hex digits with even length.
/// - Values may be empty or non-empty hex digits with even length.
/// - No `0x` prefix is accepted on either side.
/// - Duplicate keys within a single batch are rejected (the underlying
///   C++ upsert aborts on duplicates, and the error message it would
///   produce is opaque).
fn parse_pairs(arg: &str) -> Result<Vec<UpsertEntry>, String> {
    if arg.is_empty() {
        return Err("no key:value pairs provided".to_owned());
    }

    let mut entries = Vec::new();
    let mut seen_keys: std::collections::HashSet<Vec<u8>> = std::collections::HashSet::new();

    for (idx, item) in arg.split(',').enumerate() {
        let (key_hex, value_hex) = item
            .split_once(':')
            .ok_or_else(|| format!("pair {idx} ({item:?}) missing `:` separator"))?;

        if key_hex.is_empty() {
            return Err(format!("pair {idx}: empty key"));
        }
        let key = parse_hex(key_hex).map_err(|e| format!("pair {idx}: key: {e}"))?;
        let value = parse_hex(value_hex).map_err(|e| format!("pair {idx}: value: {e}"))?;

        let key_nibble_len = u8::try_from(key.len().saturating_mul(2))
            .map_err(|_| format!("pair {idx}: key too long: {} bytes", key.len()))?;

        if !seen_keys.insert(key.clone()) {
            return Err(format!("pair {idx}: duplicate key {key_hex}"));
        }

        entries.push(UpsertEntry {
            key,
            key_nibble_len,
            value,
        });
    }

    Ok(entries)
}

fn open_ro(path: &std::path::Path) -> Result<TriedbRoHandle, String> {
    TriedbRoHandle::open(path, NODE_LRU_MAX_MEM, false)
        .map_err(|e| format!("failed to open {}: {e}", path.display()))
}

fn resolve_block(handle: &TriedbRoHandle, explicit: Option<u64>) -> Result<u64, String> {
    match explicit {
        Some(b) => Ok(b),
        None => handle
            .latest_finalized_block()
            .ok_or_else(|| "no finalized block present; pass --block".to_owned()),
    }
}

/// Strict hex parser: only `[0-9a-fA-F]`, even length, no `0x` prefix.
/// Empty input yields an empty `Vec`.
fn parse_hex(s: &str) -> Result<Vec<u8>, String> {
    if s.is_empty() {
        return Ok(Vec::new());
    }
    if s.len() % 2 != 0 {
        return Err(format!("odd-length hex ({} chars)", s.len()));
    }
    hex::decode(s).map_err(|e| format!("invalid hex {s:?}: {e}"))
}

fn fmt_block(b: Option<u64>) -> String {
    match b {
        Some(n) => n.to_string(),
        None => "(none)".to_owned(),
    }
}

fn fmt_id(id: Option<[u8; 32]>) -> String {
    match id {
        Some(bytes) => format!("0x{}", hex::encode(bytes)),
        None => "(none)".to_owned(),
    }
}
