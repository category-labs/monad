#pragma once

#include <category/core/config.hpp>

#include <memory>
#include <optional>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

class FileDb final
{
    class Impl;

    std::unique_ptr<Impl> impl_;

public:
    FileDb() = delete;
    FileDb(FileDb const &) = delete;
    FileDb(FileDb &&);
    explicit FileDb(char const *dir);
    ~FileDb();

    std::optional<std::string> get(char const *key) const;

    void upsert(char const *key, std::string_view value) const;
    bool remove(char const *key) const;
};

MONAD_NAMESPACE_END
