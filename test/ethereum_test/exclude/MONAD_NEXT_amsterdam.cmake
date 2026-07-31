# Copyright (C) 2025-26 Category Labs, Inc.
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

# EIP-7708 is the last of the stacked Amsterdam EIPs, so the allowlist opens to
# the whole suite. It could not open any sooner: the bundle is generated with
# EIP-7708 active, so every fixture that moves ETH carries a Transfer log in its
# expected logs bloom, and the 109 fixtures outside amsterdam/ (reserve_balance,
# mip4_checkreservebalance, eip6780_selfdestruct, eip7702_set_code_tx, ...) fail
# with "wrong logs bloom" until the rule is live -- however complete the rest of
# the fork is. Keep using the exclusion list below for individual fixtures that
# are broken for an unrelated reason.
set(MONAD_NEXT_amsterdam_included_tests "*")
set(MONAD_NEXT_amsterdam_excluded_tests "")
