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

// Probe for -mzisk-dma. Compiled with the guest flags, the block copy must
// lower to the DMA marker, `csrs 0x813`, rather than call memcpy.

void *memcpy(void *, void const *, unsigned long);
void sink(void *);

void p(char *d, char const *s)
{
    memcpy(d, s, 512);
    sink(d);
}
