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

#pragma once

// Records each gas charge against the resource it pays for, so other gas
// schedules can be applied offline. Compiled out without MONAD_GAS_PROFILE;
// inert until a single-threaded profiling run installs a Session.

#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/result.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <type_traits>
#include <vector>

namespace monad::vm::gas_profile
{
    // [0, 256) is the static gas of each opcode, counted per execution.
    enum Component : uint16_t
    {
        MemoryWords = 256,
        MemoryWordsSquared,
        CopyCalldata,
        CopyCode,
        CopyExtcode,
        CopyReturndata,
        CopyMcopy,
        KeccakWords,
        LogBytes,
        ExpBytes,
        ColdAccount,
        ColdStorage,
        WarmDelegate,
        SstoreColdBase,
        CallValue,
        CallNewAccount,
        CallStipend,
        SelfdestructNewAccount,
        SelfdestructWarmAccess,
        CreateWords,
        Create2Words,
        CodeDepositBytes,
        SstoreStatus,
        PageWrite = SstoreStatus + 9,
        PageGrowth,
        Precompile,
        TxBase = Precompile + 32,
        TxCreate,
        TxCalldataZero,
        TxCalldataNonzero,
        TxAccessListAddress,
        TxAccessListKey,
        TxAccessListData,
        TxInitcodeWords,
        TxAuthorization,
        CodeLoadBytes,
        CodeLoadExcessBytes,
        HaltBurn,
        Untagged,
        ComponentCount
    };

    inline constexpr std::array<std::string_view, 9> sstore_status_names{
        "assigned",
        "added",
        "deleted",
        "modified",
        "deleted_added",
        "modified_deleted",
        "deleted_restored",
        "added_deleted",
        "modified_restored"};

    inline constexpr std::array<std::string_view, 32> precompile_names{
        "unknown",
        "ecrecover",
        "sha256",
        "ripemd160",
        "identity",
        "modexp",
        "ecadd",
        "ecmul",
        "ecpairing",
        "blake2f",
        "point_evaluation",
        "bls12_g1add",
        "bls12_g1msm",
        "bls12_g2add",
        "bls12_g2msm",
        "bls12_pairing",
        "bls12_map_fp_to_g1",
        "bls12_map_fp2_to_g2",
        "p256verify",
        "monad_staking",
        "monad_reserve_balance",
        "other"};

    // Precompile addresses are 0x01-0x11, 0x0100 (EIP-7951), 0x1000 (staking)
    // and 0x1001 (reserve balance).
    constexpr Component precompile_component(uint8_t const (&addr)[20])
    {
        for (int i = 0; i < 18; ++i) {
            if (addr[i] != 0) {
                return static_cast<Component>(Precompile + 21);
            }
        }
        unsigned const a = (unsigned{addr[18]} << 8) | addr[19];
        unsigned index = 21;
        if (a >= 1 && a <= 0x11) {
            index = a;
        }
        else if (a == 0x100) {
            index = 18;
        }
        else if (a == 0x1000) {
            index = 19;
        }
        else if (a == 0x1001) {
            index = 20;
        }
        return static_cast<Component>(Precompile + index);
    }

    struct Cell
    {
        int64_t count;
        int64_t units;
        int64_t gas;
    };

    struct TxRecord
    {
        std::array<Cell, ComponentCount> cells;
        int64_t tagged;
        uint64_t gas_limit;
        uint64_t intrinsic;
        int64_t exec_gas;
        uint64_t gas_used;
        uint64_t refund;
        uint32_t status;
        bool finished;
        std::vector<std::array<uint8_t, 32>> code_hashes;

        void add(Component const c, int64_t const units, int64_t const gas)
        {
            auto &cell = cells[c];
            ++cell.count;
            cell.units += units;
            cell.gas += gas;
            tagged += gas;
        }
    };

    struct Session
    {
        std::vector<TxRecord> txs;
    };

    struct Frame
    {
        int64_t gas;
        int64_t tagged;
    };

    std::string component_name(Component);

    extern Session *session;
    extern TxRecord *current;

#ifdef MONAD_GAS_PROFILE
    inline constexpr bool enabled = true;

    inline void
    charge(Component const c, int64_t const units, int64_t const gas)
    {
        if (current != nullptr) {
            current->add(c, units, gas);
        }
    }

    template <typename Gas>
    [[nodiscard]] Gas tag(Component const c, int64_t const units, Gas const gas)
    {
        if constexpr (std::is_integral_v<Gas>) {
            charge(c, units, gas);
        }
        else {
            charge(c, units, *gas);
        }
        return gas;
    }

    // Code bytes a transaction loads, once per code hash: the quantity a
    // code-size-aware price (EIP-7907) would charge for. Free today.
    inline void code_load(uint8_t const (&hash)[32], size_t const size)
    {
        if (current == nullptr || size == 0) {
            return;
        }
        std::array<uint8_t, 32> key;
        std::copy_n(hash, 32, key.begin());
        for (auto const &seen : current->code_hashes) {
            if (seen == key) {
                return;
            }
        }
        current->code_hashes.push_back(key);
        auto const bytes = static_cast<int64_t>(size);
        current->add(CodeLoadBytes, bytes, 0);
        if (bytes > 0x6000) {
            current->add(CodeLoadExcessBytes, bytes - 0x6000, 0);
        }
    }

    inline Frame frame_enter(int64_t const gas)
    {
        return {gas, current != nullptr ? current->tagged : 0};
    }

    // Gas a frame consumed that no charge accounts for: the gas an
    // exceptional halt burns, or a charge site that is not instrumented.
    inline void
    frame_exit(Frame const f, int64_t const gas_left, bool const exceptional)
    {
        if (current == nullptr) {
            return;
        }
        int64_t const residual =
            (f.gas - gas_left) - (current->tagged - f.tagged);
        if (residual != 0) {
            current->add(exceptional ? HaltBurn : Untagged, residual, residual);
        }
    }

    inline void frame_exit(Frame const f, Result const &result)
    {
        frame_exit(
            f,
            result.gas_left,
            result.status_code != CallStatus::Success &&
                result.status_code != CallStatus::Revert);
    }

    inline void tx_begin(uint64_t const i, uint64_t const gas_limit)
    {
        if (session == nullptr) {
            return;
        }
        current = nullptr;
        if (session->txs.size() <= i) {
            session->txs.resize(i + 1);
        }
        auto &rec = session->txs[i];
        rec = TxRecord{};
        rec.gas_limit = gas_limit;
        current = &rec;
    }

    inline void tx_exec(uint64_t const intrinsic, int64_t const exec_gas)
    {
        if (current != nullptr) {
            current->intrinsic = intrinsic;
            current->exec_gas = exec_gas;
        }
    }

    inline void tx_end(
        uint64_t const i, uint64_t const gas_used, uint64_t const refund,
        uint32_t const status)
    {
        if (session == nullptr) {
            return;
        }
        current = nullptr;
        if (session->txs.size() <= i) {
            return;
        }
        auto &rec = session->txs[i];
        rec.gas_used = gas_used;
        rec.refund = refund;
        rec.status = status;
        rec.finished = true;
    }
#else
    inline constexpr bool enabled = false;

    inline void charge(Component, int64_t, int64_t) {}

    template <typename Gas>
    [[nodiscard]] Gas tag(Component, int64_t, Gas const gas)
    {
        return gas;
    }

    inline void code_load(uint8_t const (&)[32], size_t) {}

    inline Frame frame_enter(int64_t)
    {
        return {};
    }

    inline void frame_exit(Frame, int64_t, bool) {}

    inline void frame_exit(Frame, Result const &) {}

    inline void tx_begin(uint64_t, uint64_t) {}

    inline void tx_exec(uint64_t, int64_t) {}

    inline void tx_end(uint64_t, uint64_t, uint64_t, uint32_t) {}
#endif
}
