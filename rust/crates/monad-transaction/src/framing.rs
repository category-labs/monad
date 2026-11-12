// Copyright (C) 2025 Category Labs, Inc.
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

use alloy_eips::eip2718::{Decodable2718, Eip2718Error, Eip2718Result};
use alloy_rlp::Header;

use crate::native::finish;

/// Decode one block/IPC RLP item without allowing its decoder to read a sibling.
/// Legacy envelopes are lists; typed envelopes are strings containing type || body.
pub(crate) fn network_decode<T: Decodable2718>(buf: &mut &[u8]) -> Eip2718Result<T> {
    let original = *buf;
    let mut after_header = original;
    let header = Header::decode(&mut after_header)?;
    // Header::decode checks that the full declared payload is present.
    let (payload, rest) = after_header.split_at(header.payload_length);
    let value = if header.list {
        let mut item = &original[..original.len() - rest.len()];
        let value = T::fallback_decode(&mut item)?;
        finish(item)?;
        value
    } else {
        let (&ty, mut body) = payload
            .split_first()
            .ok_or(alloy_rlp::Error::InputTooShort)?;
        if !(1..=0x7f).contains(&ty) {
            return Err(Eip2718Error::UnexpectedType(ty));
        }
        let value = T::typed_decode(ty, &mut body)?;
        finish(body)?;
        value
    };
    *buf = rest;
    Ok(value)
}
