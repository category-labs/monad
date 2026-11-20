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

//! Helpers for legacy Ethereum-only test fixtures. Not a live-ring migration API.
use std::io::{Cursor, Read};

use monad_event_ring::EventDecoder;

use crate::ExecEventDecoder;

/// Reframe a pre-0x40 test snapshot for the current decoder without changing its
/// payload. The new u8 presence flag occupies old padding and is read only for
/// native transactions, which these historical fixtures do not contain.
/// Production ring readers continue to require the exact current schema hash.
pub fn upgrade_legacy_snapshot(bytes: &[u8]) -> Vec<u8> {
    const LEGACY_SCHEMA: [u8; 32] = [
        0x89, 0x33, 0xf9, 0x07, 0xc4, 0x32, 0xc9, 0x8a, 0xc0, 0xc8, 0xdb, 0x62, 0xf9, 0xaa, 0x16,
        0x4c, 0x0c, 0x3f, 0x16, 0x72, 0xf4, 0x12, 0x90, 0xe4, 0xea, 0x34, 0x08, 0xdf, 0x6c, 0x67,
        0x23, 0xf3,
    ];
    let mut decoder = zstd::stream::read::Decoder::new(bytes).unwrap();
    let mut header = [0u8; 40];
    decoder.read_exact(&mut header).unwrap();
    assert_eq!(&header[..4], b"RING");
    assert_eq!(&header[8..], &LEGACY_SCHEMA);
    header[8..].copy_from_slice(ExecEventDecoder::ring_schema_hash());
    zstd::stream::encode_all(Cursor::new(header).chain(decoder), 1).unwrap()
}
