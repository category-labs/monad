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

// The undo journal of the guest state: the open call frames, the records
// that roll a frame back, and the logs a frame may discard.
//
// A frame is a mark into one append-only log of undo records. Every mutation
// records what it overwrote while a frame is open and nothing otherwise, so
// the block prologue and the end-of-transaction walks cost no journal at
// all. pop_accept drops the mark and keeps the records, since the parent may
// still roll them back; pop_reject replays the records above the mark
// backwards, so the oldest value is restored last, and truncates. Records
// point at rows, which never move.
//
// Header-only: the record methods sit on every write path and the compiler
// is to see through them into the State.

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <zkvm/state/account_state.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace zkvm
{
    class Journal
    {
        // Each record names the row and carries either its old value in
        // `aux` (Nonce, slot positions) or an index into the payload vector
        // of its kind. Flags are recorded on the false-to-true transition
        // only.
        enum class UndoKind : uint8_t
        {
            // The write materialised the account: back to nullopt. The row
            // stays, since the trie answer it caches is still valid.
            Created,
            // accounts_[aux]: the whole previous account, for a changed
            // incarnation.
            Account,
            // words_[aux]: the previous balance, as raw bytes.
            Balance,
            // aux: the previous nonce.
            Nonce,
            // words_[aux]: the previous code hash.
            CodeHash,
            Accessed,
            Touched,
            Destructed,
            // aux: the slot's position in the row's storage.
            SlotWarm,
            // aux: the slot's position; the write set `written`.
            SlotCreated,
            // slots_[aux]: the slot's previous value, tx_start and stamp.
            SlotValue,
            // slots_[aux]: the transient slot's previous value.
            Transient,
        };

        struct Undo
        {
            AccountState *account_state;
            UndoKind kind;
            uint64_t aux;
            // Power-of-two size, so size() is a shift.
            uint64_t pad_;
        };

        static_assert(sizeof(Undo) == 32);

        struct SlotUndo
        {
            bytes32_t value;
            bytes32_t tx_start;
            Incarnation incarnation{0, 0};
            uint32_t pos;
            unsigned char pad_
                [128 - 2 * sizeof(bytes32_t) - sizeof(Incarnation) -
                 sizeof(uint32_t)];
        };

        static_assert(sizeof(SlotUndo) == 128);

        // Watermarks of one open call frame: the sizes to truncate the
        // journal and the logs back to on pop_reject.
        struct Mark
        {
            size_t undo;
            size_t accounts;
            size_t words;
            size_t slots;
            size_t logs;
            size_t pad_[3];
        };

        static_assert(sizeof(Mark) == 64);

        // Initial capacities: the guest's arena never frees, so growth is a
        // copy and a leak.
        static constexpr size_t UNDO_RESERVE = 256;
        static constexpr size_t MARKS_RESERVE = 64;
        static constexpr size_t LOGS_RESERVE = 64;

        std::vector<Undo> undo_;
        std::vector<std::optional<Account>> accounts_;
        std::vector<bytes32_t> words_;
        std::vector<SlotUndo> slots_;
        std::vector<Mark> marks_;
        std::vector<Receipt::Log> logs_;

        void record(
            AccountState &account_state, UndoKind const kind,
            uint64_t const aux = 0)
        {
            if (open()) {
                undo_.push_back(Undo{
                    .account_state = &account_state, .kind = kind, .aux = aux});
            }
        }

        void record_word(
            AccountState &account_state, UndoKind const kind,
            bytes32_t const &word)
        {
            if (open()) {
                record(account_state, kind, words_.size());
                words_.push_back(word);
            }
        }

        void record_slot(
            AccountState &account_state, UndoKind const kind,
            SlotUndo const &slot)
        {
            if (open()) {
                record(account_state, kind, slots_.size());
                slots_.push_back(slot);
            }
        }

        void clear()
        {
            undo_.clear();
            accounts_.clear();
            words_.clear();
            slots_.clear();
        }

    public:
        Journal()
        {
            undo_.reserve(UNDO_RESERVE);
            accounts_.reserve(MARKS_RESERVE);
            words_.reserve(UNDO_RESERVE);
            slots_.reserve(UNDO_RESERVE);
            marks_.reserve(MARKS_RESERVE);
            logs_.reserve(LOGS_RESERVE);
        }

        Journal(Journal &&) = delete;
        Journal(Journal const &) = delete;
        Journal &operator=(Journal &&) = delete;
        Journal &operator=(Journal const &) = delete;

        ////////////////////////////////////////
        // Frames

        // Whether any frame is open, i.e. anything could still roll back.
        [[nodiscard]] bool open() const noexcept
        {
            return !marks_.empty();
        }

        void push()
        {
            marks_.push_back(Mark{
                .undo = undo_.size(),
                .accounts = accounts_.size(),
                .words = words_.size(),
                .slots = slots_.size(),
                .logs = logs_.size()});
        }

        void pop_accept()
        {
            MONAD_ASSERT(open(), "zkvm State: pop without push");
            // The parent frame may still roll the records back, so they stay
            // until the last frame closes.
            marks_.pop_back();
            if (!open()) {
                clear();
            }
        }

        void pop_reject()
        {
            MONAD_ASSERT(open(), "zkvm State: pop without push");
            Mark const mark = marks_.back();
            marks_.pop_back();
            // Replay backwards, so that the oldest value is restored last.
            while (undo_.size() > mark.undo) {
                Undo const &u = undo_.back();
                AccountState &account_state = *u.account_state;
                switch (u.kind) {
                case UndoKind::Created:
                    account_state.account_.reset();
                    break;
                case UndoKind::Account:
                    account_state.account_ = accounts_[u.aux];
                    break;
                case UndoKind::Balance:
                    // Raw bytes, saved and restored verbatim: a copy, not a
                    // conversion. The account's creation precedes the write,
                    // so reverse replay still finds it.
                    MONAD_ASSERT(account_state.account_.has_value());
                    static_assert(
                        sizeof(account_state.account_->balance) ==
                        sizeof(bytes32_t));
                    std::memcpy(
                        &account_state.account_->balance,
                        words_[u.aux].bytes,
                        sizeof(bytes32_t));
                    break;
                case UndoKind::Nonce:
                    MONAD_ASSERT(account_state.account_.has_value());
                    account_state.account_->nonce = u.aux;
                    break;
                case UndoKind::CodeHash:
                    MONAD_ASSERT(account_state.account_.has_value());
                    account_state.account_->code_hash = words_[u.aux];
                    break;
                case UndoKind::Accessed:
                    account_state.accessed = false;
                    break;
                case UndoKind::Touched:
                    account_state.touched = false;
                    break;
                case UndoKind::Destructed:
                    account_state.destructed = false;
                    break;
                case UndoKind::SlotWarm:
                    account_state.storage.at(u.aux).accessed = false;
                    break;
                case UndoKind::SlotCreated:
                    account_state.storage.at(u.aux).written = false;
                    break;
                case UndoKind::SlotValue: {
                    SlotUndo const &su = slots_[u.aux];
                    SlotState &s = account_state.storage.at(su.pos);
                    s.current = su.value;
                    s.tx_start = su.tx_start;
                    s.incarnation = su.incarnation;
                    break;
                }
                case UndoKind::Transient: {
                    SlotUndo const &su = slots_[u.aux];
                    account_state.transient_storage.at(su.pos).value = su.value;
                    break;
                }
                }
                undo_.pop_back();
            }
            accounts_.resize(mark.accounts);
            words_.resize(mark.words);
            slots_.resize(mark.slots);
            logs_.resize(mark.logs);
            if (!open()) {
                clear();
            }
        }

        ////////////////////////////////////////
        // Records, each a no-op while no frame is open. Called before the
        // mutation they describe, with the values about to be overwritten.

        void created(AccountState &account_state)
        {
            record(account_state, UndoKind::Created);
        }

        void account(AccountState &account_state)
        {
            if (open()) {
                record(account_state, UndoKind::Account, accounts_.size());
                accounts_.push_back(account_state.account_);
            }
        }

        void balance(AccountState &account_state, uint256_t const &previous)
        {
            record_word(account_state, UndoKind::Balance, to_bytes(previous));
        }

        void nonce(AccountState &account_state, uint64_t const previous)
        {
            record(account_state, UndoKind::Nonce, previous);
        }

        void code_hash(AccountState &account_state, bytes32_t const &previous)
        {
            record_word(account_state, UndoKind::CodeHash, previous);
        }

        void accessed(AccountState &account_state)
        {
            record(account_state, UndoKind::Accessed);
        }

        void touched(AccountState &account_state)
        {
            record(account_state, UndoKind::Touched);
        }

        void destructed(AccountState &account_state)
        {
            record(account_state, UndoKind::Destructed);
        }

        void slot_warm(AccountState &account_state, SlotState const &s)
        {
            record(
                account_state,
                UndoKind::SlotWarm,
                account_state.storage.index_of(s));
        }

        void slot_created(AccountState &account_state, SlotState const &s)
        {
            record(
                account_state,
                UndoKind::SlotCreated,
                account_state.storage.index_of(s));
        }

        void slot_value(AccountState &account_state, SlotState const &s)
        {
            record_slot(
                account_state,
                UndoKind::SlotValue,
                SlotUndo{
                    .value = s.current,
                    .tx_start = s.tx_start,
                    .incarnation = s.incarnation,
                    .pos = static_cast<uint32_t>(
                        account_state.storage.index_of(s))});
        }

        void transient(AccountState &account_state, TransientSlot const &t)
        {
            record_slot(
                account_state,
                UndoKind::Transient,
                SlotUndo{
                    .value = t.value,
                    .tx_start = {},
                    .pos = static_cast<uint32_t>(
                        account_state.transient_storage.index_of(t))});
        }

        ////////////////////////////////////////
        // Logs: append-only, cut back to the mark on pop_reject.

        [[nodiscard]] std::span<Receipt::Log const> logs() const noexcept
        {
            return logs_;
        }

        void store_log(Receipt::Log const &log)
        {
            logs_.push_back(log);
        }

        // Hand the logs over; no frame may be open.
        std::vector<Receipt::Log> take_logs()
        {
            MONAD_ASSERT(!open(), "zkvm State: frame open at tx end");
            std::vector<Receipt::Log> taken;
            taken.swap(logs_);
            logs_.reserve(LOGS_RESERVE);
            return taken;
        }
    };
}

MONAD_NAMESPACE_END
