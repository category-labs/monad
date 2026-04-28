# Copyright (C) 2025 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

obj = "libmonad_core_disas.a"
syms = [
    "monad::addc_disas(unsigned long, unsigned long, bool)",
    "monad::subb_disas(unsigned long, unsigned long, bool)",
    "monad::shld_disas(unsigned long, unsigned long, unsigned char)",
    "monad::shrd_disas(unsigned long, unsigned long, unsigned char)",
    "monad::div_disas(unsigned long, unsigned long, unsigned long)",
    "monad::mulx_disas(unsigned long, unsigned long, unsigned long&, unsigned long&)",
    "monad::uint256_add_disas(monad::vm::runtime::uint256_t const&, monad::vm::runtime::uint256_t const&)",
    "monad::uint256_sub_disas(monad::vm::runtime::uint256_t const&, monad::vm::runtime::uint256_t const&)",
    "monad::uint256_mul_disas(monad::vm::runtime::uint256_t const&, monad::vm::runtime::uint256_t const&)",
    "monad::uint256_shl_disas(monad::vm::runtime::uint256_t const&, unsigned long)",
    "monad::uint256_shr_disas(monad::vm::runtime::uint256_t const&, monad::vm::runtime::uint256_t const&)",
    "monad::uint256_div_disas(monad::vm::runtime::uint256_t const&, monad::vm::runtime::uint256_t const&)",
    "monad::uint256_swap_disas(monad::vm::runtime::uint256_t&, monad::vm::runtime::uint256_t&)",
]
