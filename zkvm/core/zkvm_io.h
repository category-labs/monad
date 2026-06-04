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

/**
 * zkVM IO C Interface
 *
 * This header defines the standard C interface for guest programs to access
 * private input and write public output.
 *
 * The functions follow:
 * https://github.com/eth-act/zkvm-standards/tree/main/standards/io-interface
 *
 * Vendored from ZisK v0.18.0:
 *   https://github.com/0xPolygonHermez/zisk/blob/v0.18.0/zkvm-interface/zkvm_io.h
 *
 * Implementation is supplied at link time by the backend:
 *   - ZisK: ziskos (entrypoint crate) provides read_input / write_output via
 *     zisklib::zkvm_io and the eth-act-standard symbols.
 *   - SP1: libzkevm.a (built from the SP1 zkEVM SDK source; see
 *     zkvm/build-support) provides read_input / write_output natively.
 */

#ifndef ZKVM_IO_H
#define ZKVM_IO_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

/**
 * Return the private input buffer.
 *
 * The returned pointer is read-only from the guest's perspective. The function
 * is idempotent and may be called multiple times.
 *
 * On ZisK this exposes the first logical stdin record and does not advance
 * ZisK's streaming input cursor. Guest programs should use either this standard
 * IO interface or ZisK's streaming input APIs for a given input, not both.
 *
 * @param[out] buf_ptr Pointer receiving the input buffer address
 * @param[out] buf_size Pointer receiving the input buffer size in bytes
 */
void read_input(uint8_t const **buf_ptr, size_t *buf_size);

/**
 * Append bytes to the public output.
 *
 * Multiple calls are observed as if their byte buffers were concatenated.
 *
 * @param output Pointer to readable bytes
 * @param size Number of bytes to append
 */
void write_output(uint8_t const *output, size_t size);

#ifdef __cplusplus
}
#endif

#endif /* ZKVM_IO_H */
