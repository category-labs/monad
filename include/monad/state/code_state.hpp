#pragma once

#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <monad/state/config.hpp>
#include <monad/state/datum.hpp>

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
    static inline byte_string const empty{};

    CodeState(TCodeDB &s)
        : db_{s}
    {
    }

    [[nodiscard]] byte_string_view code_at(bytes32_t const &b) const
    {
        if (merged_.contains(b)) {
            return {merged_.at(b)};
        }
        if (db_.contains(b)) {
            return {db_.at(b)};
        }
        return {empty};
    }

    [[nodiscard]] bool can_merge(ChangeSet const &w) const
    {
        return std::ranges::none_of(w.code_, [&](auto const &a) {
            return merged_.contains(a.first) || db_.contains(a.first);
        });
    }

    void merge_changes(ChangeSet &w)
    {
        assert(can_merge(w));

        for (auto &[a, code] : w.code_) {
            auto const &[_, inserted] = merged_.emplace(a, std::move(code));
            MONAD_DEBUG_ASSERT(inserted);
        }
    }

    [[nodiscard]] bool can_commit() const
    {
        return std::ranges::none_of(
            merged_, [&](auto const &a) { return db_.contains(a.first); });
    }

    void commit_all_merged()
    {
        assert(can_commit());

        for (auto &[a, code] : merged_) {
            auto const &[_, inserted] = db_.emplace(a, std::move(code));
            MONAD_DEBUG_ASSERT(inserted);
        }
        merged_.clear();
    }
};

template <typename TCodeDB>
struct CodeState<TCodeDB>::ChangeSet : public CodeState<TCodeDB>
{
    map_t code_{};

    explicit ChangeSet(CodeState const &c)
        : CodeState(c)
    {
    }

    [[nodiscard]] byte_string_view const
    code_at(bytes32_t const &b) const noexcept
    {
        if (code_.contains(b))
            return {code_.at(b)};
        return CodeState::code_at(b);
    }

    void set_code(bytes32_t const &b, byte_string const &code)
    {
        if (code.empty()) {
            return;
        }
        auto const &[_, inserted] = code_.emplace(b, code);
        MONAD_DEBUG_ASSERT(inserted);
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
        assert(code.size() > offset);
        auto const bytes_to_copy = std::min(code.size() - offset, buffer_size);
        std::memcpy(buffer, code.begin() + offset, bytes_to_copy);
        return bytes_to_copy;
    }

    void revert() { code_.clear(); }
};

MONAD_STATE_NAMESPACE_END
