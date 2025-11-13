// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/config.hpp>

#include <chrono>

MONAD_NAMESPACE_BEGIN

class BlockMetrics
{
    uint32_t n_retries_{0};
    uint32_t account_touched_{0};
    uint32_t account_changed_{0};
    uint32_t storage_touched_{0};
    uint32_t storage_changed_{0};
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

    uint32_t num_account_touched() const
    {
        return account_touched_;
    }

    uint32_t num_account_changed() const
    {
        return account_changed_;
    }

    uint32_t num_storage_touched() const
    {
        return storage_touched_;
    }

    uint32_t num_storage_changed() const
    {
        return storage_changed_;
    }

    void set_tx_exec_time(std::chrono::microseconds const exec_time)
    {
        tx_exec_time_ = exec_time;
    }

    std::chrono::microseconds tx_exec_time() const
    {
        return tx_exec_time_;
    }

    void add_account_touched(uint32_t const value)
    {
        account_touched_ += value;
    }

    void add_account_changed(uint32_t const value)
    {
        account_changed_ += value;
    }

    void add_storage_touched(uint32_t const value)
    {
        storage_touched_ += value;
    }

    void add_storage_changed(uint32_t const value)
    {
        storage_changed_ += value;
    }
};

MONAD_NAMESPACE_END
