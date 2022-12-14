#pragma once

#include <monad/config.hpp>

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
    FileDb(char const *dir);
    ~FileDb();

    std::optional<std::string> get(char const *key) const;

    void upsert(char const *key, std::string_view value) const;
    void remove(char const *key) const;
};

MONAD_NAMESPACE_END
