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

use std::mem::MaybeUninit;

/// Safely casts the beginning chunk of the provided byte slice `bytes` into a `&T` if possible,
/// producing the remaining half of the slice alongside in a tuple.
fn split_ref_from_bytes<T>(bytes: &'_ [u8]) -> Result<(&'_ T, &'_ [u8]), String> {
    let Some((bytes, rest)) = bytes.split_at_checked(size_of::<T>()) else {
        return Err(format!(
            "Expected slice with length at least {} but slice has length {}",
            size_of::<T>(),
            bytes.len()
        ));
    };

    assert_eq!(bytes.len(), size_of::<T>());

    let bytes_ptr = bytes.as_ptr();

    if (bytes_ptr as usize) % align_of::<T>() != 0 {
        return Err(format!(
            "Expected slice with alignment {} but slice has ptr {}",
            align_of::<T>(),
            bytes_ptr as usize
        ));
    }

    Ok((unsafe { &*(bytes_ptr as *const T) }, rest))
}

/// Safely casts the provided byte slice `bytes` into a `&T`.
pub(crate) fn ref_from_bytes<T>(bytes: &'_ [u8]) -> Result<&'_ T, String> {
    let (value_ref, rest) = split_ref_from_bytes(bytes)?;

    if !rest.is_empty() {
        return Err(format!(
            "Expected slice with length {} but slice has length {}",
            size_of::<T>(),
            bytes.len()
        ));
    }

    Ok(value_ref)
}

/// Safely casts the provided byte slice `bytes` into a `&T` and produces it along with an array of
/// trailing byte slices from sizes specified using the produced `&T`.
///
/// Some execution events specify trailing byte data, like
/// [`ExecEventsRef::TxnStart`](crate::ExecEventsRef), whose size can only be determined after first
/// parsing the event, [`monad_exec_txn_start`](crate::ffi::monad_exec_txn_start). This function
/// takes a fn which, given this `&T` reference, produces an array of trailing byte sizes which are
/// subsequently split out and produced alongside the `&T`.
pub(crate) fn ref_from_bytes_with_trailing<'ring, T, const N: usize>(
    bytes: &'ring [u8],
    trailing_lengths: impl FnOnce(&T) -> [usize; N],
) -> Result<(&'ring T, [&'ring [u8]; N]), String> {
    let (value, mut bytes) = split_ref_from_bytes::<T>(bytes)?;

    let trailing_lengths = trailing_lengths(value);

    let mut trailing: [MaybeUninit<&'ring [u8]>; N] =
        unsafe { MaybeUninit::uninit().assume_init() };

    for (idx, length) in trailing_lengths.into_iter().enumerate() {
        let Some((bytes_next, bytes_rest)) = bytes.split_at_checked(length) else {
            return Err(format!(
                "Expected slice with length greater than {length} but slice has length {}",
                bytes.len()
            ));
        };

        trailing[idx] = MaybeUninit::new(bytes_next);
        bytes = bytes_rest;
    }

    if !bytes.is_empty() {
        return Err(format!(
            "Payload trailing slice has {} additional bytes",
            bytes.len()
        ));
    }

    let trailing = std::array::from_fn(|i| unsafe { trailing[i].assume_init() });

    Ok((value, trailing))
}
