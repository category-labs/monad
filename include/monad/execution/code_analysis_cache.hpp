#pragma once

#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>

#include <evmone/baseline.hpp>

#include <memory>
#include <utility>

MONAD_NAMESPACE_BEGIN

class CodeAnalysisCache
{
private:
    class Impl;

    std::unique_ptr<Impl> const impl_;

public:
    CodeAnalysisCache();
    ~CodeAnalysisCache();

    std::shared_ptr<evmone::baseline::CodeAnalysis> get(bytes32_t const &hash);
    std::shared_ptr<evmone::baseline::CodeAnalysis>
    put(bytes32_t const &hash, evmone::baseline::CodeAnalysis &&);

    std::pair<size_t, size_t> hit_rate() const;
};

MONAD_NAMESPACE_END
