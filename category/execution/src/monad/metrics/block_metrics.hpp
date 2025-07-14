#pragma once

#include <category/core/config.hpp>

#include <chrono>

MONAD_NAMESPACE_BEGIN

class BlockMetrics
{
    uint32_t n_retries_{0};
    std::chrono::microseconds tx_exec_time_{1};

public:
    void inc_retries()
    {
        ++n_retries_;
    }

    uint32_t num_retries() const
    {
        return n_retries_;
    }

    void set_tx_exec_time(std::chrono::microseconds const exec_time)
    {
        tx_exec_time_ = exec_time;
    }

    std::chrono::microseconds tx_exec_time() const
    {
        return tx_exec_time_;
    }
};

MONAD_NAMESPACE_END
