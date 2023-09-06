#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <monad/state/config.hpp>
#include <monad/state/datum.hpp>
#include <monad/state/state_changes.hpp>

#include <algorithm>
#include <unordered_map>

MONAD_STATE_NAMESPACE_BEGIN

template <typename TError>
class error;

template <class TCodeDB>
struct CodeState
{
    using map_t = std::unordered_map<bytes32_t, byte_string>;

    struct ChangeSet;

    TCodeDB &db_;
    map_t merged_{};

    CodeState(TCodeDB &s)
        : db_{s}
    {
    }

    [[nodiscard]] byte_string code_at(bytes32_t const &b) const
    {
        if (merged_.contains(b)) {
            return merged_.at(b);
        }
        return db_.read_code(b);
    }

    [[nodiscard]] bool can_merge(ChangeSet const &w) const
    {
        return std::ranges::all_of(w.code_, [&](auto const &a) {
            auto const &existing_value = code_at(a.first);
            return existing_value.empty() || a.second == existing_value;
        });
    }

    void merge_changes(ChangeSet &w)
    {
        assert(can_merge(w));

        for (auto &[code_hash, code] : w.code_) {
            merged_.emplace(code_hash, std::move(code));
        }
    }

    [[nodiscard]] bool can_commit() const
    {
        return std::ranges::none_of(merged_, [&](auto const &a) {
            return !db_.read_code(a.first).empty();
        });
    }

    [[nodiscard]] StateChanges::CodeChanges gather_changes() const
    {
        assert(can_commit());
        StateChanges::CodeChanges code_changes;

        for (auto &[code_hash, code] : merged_) {
            code_changes.emplace_back(code_hash, std::move(code));
        }

        return code_changes;
    }

    void clear_changes() { merged_.clear(); }
};

template <typename TCodeDB>
struct CodeState<TCodeDB>::ChangeSet : public CodeState<TCodeDB>
{
    map_t code_{};

    explicit ChangeSet(CodeState const &c)
        : CodeState(c)
    {
    }

    [[nodiscard]] byte_string const code_at(bytes32_t const &b) const noexcept
    {
        if (code_.contains(b))
            return {code_.at(b)};
        return CodeState::code_at(b);
    }

    void set_code(bytes32_t const &code_hash, byte_string const &code)
    {
        if (code.empty()) {
            return;
        }
        auto const &[_, inserted] = code_.emplace(code_hash, code);
        if (!inserted) {
            MONAD_DEBUG_ASSERT(code_.at(code_hash) == code);
        }
    }

    [[nodiscard]] size_t get_code_size(bytes32_t const &b) const noexcept
    {
        return code_at(b).size();
    }

    [[nodiscard]] size_t copy_code(
        bytes32_t const &b, size_t offset, uint8_t *buffer,
        size_t buffer_size) const
    {
        auto const code = code_at(b);

        if (offset >= code.size()) {
            return 0;
        }

        auto const bytes_to_copy = std::min(code.size() - offset, buffer_size);
        std::copy_n(
            std::next(code.begin(), static_cast<long>(offset)),
            bytes_to_copy,
            buffer);
        return bytes_to_copy;
    }

    void revert() { code_.clear(); }
};

MONAD_STATE_NAMESPACE_END
