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

#include <category/vm/gas_profile.hpp>

#include <string>

namespace monad::vm::gas_profile
{
    Session *session = nullptr;
    TxRecord *current = nullptr;

    std::string component_name(Component const c)
    {
        if (c >= SstoreStatus && c < PageWrite) {
            return "sstore:" +
                   std::string{sstore_status_names[c - SstoreStatus]};
        }
        if (c >= Precompile && c < TxBase) {
            auto const name = precompile_names[c - Precompile];
            return name.empty() ? "precompile:" + std::to_string(c - Precompile)
                                : "precompile:" + std::string{name};
        }
        switch (c) {
        case MemoryWords:
            return "mem:words";
        case MemoryWordsSquared:
            return "mem:words_sq";
        case CopyCalldata:
            return "copy:calldata";
        case CopyCode:
            return "copy:code";
        case CopyExtcode:
            return "copy:extcode";
        case CopyReturndata:
            return "copy:returndata";
        case CopyMcopy:
            return "copy:mcopy";
        case KeccakWords:
            return "keccak:words";
        case LogBytes:
            return "log:bytes";
        case ExpBytes:
            return "exp:bytes";
        case ColdAccount:
            return "access:cold_account";
        case ColdStorage:
            return "access:cold_storage";
        case WarmDelegate:
            return "access:warm_delegate";
        case SstoreColdBase:
            return "sstore:cold_base";
        case CallValue:
            return "call:value";
        case CallNewAccount:
            return "call:new_account";
        case CallStipend:
            return "call:stipend";
        case SelfdestructNewAccount:
            return "selfdestruct:new_account";
        case SelfdestructWarmAccess:
            return "selfdestruct:warm_access";
        case CreateWords:
            return "create:words";
        case Create2Words:
            return "create2:words";
        case CodeDepositBytes:
            return "create:deposit_bytes";
        case PageWrite:
            return "sstore:page_write";
        case PageGrowth:
            return "sstore:page_growth";
        case TxBase:
            return "tx:base";
        case TxCreate:
            return "tx:create";
        case TxCalldataZero:
            return "tx:calldata_zero";
        case TxCalldataNonzero:
            return "tx:calldata_nonzero";
        case TxAccessListAddress:
            return "tx:access_list_address";
        case TxAccessListKey:
            return "tx:access_list_key";
        case TxAccessListData:
            return "tx:access_list_data";
        case TxInitcodeWords:
            return "tx:initcode_words";
        case TxAuthorization:
            return "tx:authorization";
        case CodeLoadBytes:
            return "code:load_bytes";
        case CodeLoadExcessBytes:
            return "code:load_excess_bytes";
        case HaltBurn:
            return "halt:burn";
        case Untagged:
            return "untagged";
        default:
            return "op:" + std::to_string(static_cast<unsigned>(c));
        }
    }
}
