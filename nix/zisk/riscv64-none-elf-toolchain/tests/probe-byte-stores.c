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

// Probe for -mzisk-clean-byte-stores. The byte constant must load as
// `li ...,184` rather than -72, and the byte addition must become
// `addi ...,...,128` rather than -128.

void f(unsigned char *p)
{
    *p = 0xb8;
}

void g(unsigned char *p, unsigned char n)
{
    *p = 0x80 + n;
}
