#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>

#include <monad/db/config.hpp>
#include <monad/db/datum.hpp>

#include <algorithm>
#include <unordered_map>

MONAD_DB_NAMESPACE_BEGIN

template <typename TError>
class error;

template <class TCodeDB>
struct CodeStore
{
    using map_t = std::unordered_map<address_t, byte_string>;

    struct WorkingCopy;

    TCodeDB &db_;
    map_t merged_{};
    static inline byte_string const empty{};

    CodeStore(TCodeDB &s)
        : db_{s}
    {
    }

    [[nodiscard]] byte_string const &code_at(address_t const &a) const
    {
        if (merged_.contains(a)) {
            return merged_.at(a);
        }
        if (db_.contains(a)) {
            return db_.at(a);
        }
        return empty;
    }

    [[nodiscard]] bool can_merge(WorkingCopy const &w) const
    {
        return std::ranges::none_of(w.code_, [&](auto const &a) {
           return merged_.contains(a.first) || db_.contains(a.first);
        });
    }

    void merge_changes(WorkingCopy &w)
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
struct CodeStore<TCodeDB>::WorkingCopy : public CodeStore<TCodeDB>
{
    map_t code_{};

    explicit WorkingCopy(CodeStore const &c)
        : CodeStore(c)
    {
    }

    [[nodiscard]] byte_string const &code_at(address_t const &a) const noexcept
    {
        if (code_.contains(a))
            return code_.at(a);
        return CodeStore::code_at(a);
    }

    void set_code(address_t const &a, byte_string const &code)
    {
        if (code.empty()) {
            return;
        }
        auto const &[_, inserted] = code_.emplace(a, code);
        MONAD_DEBUG_ASSERT(inserted);
    }

    // EVMC Host Interface
    [[nodiscard]] size_t get_code_size(address_t const &a) const noexcept
    {
        return code_at(a).size();
    }

    // EVMC Host Interface
    [[nodiscard]] size_t copy_code(
        address_t const &a, size_t offset, uint8_t *buffer, size_t buffer_size)
    {
        auto const &code = code_at(a);
        assert(code.size() > offset);
        auto const bytes_to_copy = std::min(code.size() - offset, buffer_size);
        std::memcpy(buffer, code.c_str() + offset, bytes_to_copy);
        return bytes_to_copy;
    }

    void revert() { code_.clear(); }
};

MONAD_DB_NAMESPACE_END
