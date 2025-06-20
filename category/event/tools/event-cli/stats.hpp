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

/**
 * @file
 *
 * This file defines interfaces for computing online (i.e., incremental)
 * statistics
 */

#include <algorithm>
#include <concepts>
#include <cstdio>
#include <span>
#include <vector>

#include <category/core/assert.h>

/**
 * Implementation of the TDigest algorithm from
 *
 *   Computing Extremely Accurate Quantiles Using t-Digests
 *       [arXiv:1902.04023 [stat.CO]]
 */
class TDigest
{
public:
    TDigest();

    void add(double);

    template <std::convertible_to<double> T>
    void merge_sorted_points(std::span<T const>, T *incoming_sum);

    double compute_quantile(double q) const;

    size_t num_centroids() const
    {
        return centroids_.size();
    }

    void set_compression(double c)
    {
        compression_ = c;
    }

    void dump(std::FILE *);

private:
    struct Centroid
    {
        double sum;
        size_t weight;

        double mean() const
        {
            return sum / static_cast<double>(weight);
        }

        double half_weight() const
        {
            return static_cast<double>(weight) / 2.0;
        }

        bool is_unit_weight() const
        {
            return weight == 1;
        }
    };

    void merge_centroids(std::span<Centroid const>, size_t input_weight);

    std::vector<Centroid> centroids_;
    std::vector<Centroid> prealloc_points_;
    std::vector<Centroid> merge_buf_;
    double compression_;
    double min_;
    double max_;
    size_t total_weight_;
};

template <std::convertible_to<double> T>
void TDigest::merge_sorted_points(std::span<T const> points, T *incoming_sum)
{
    MONAD_DEBUG_ASSERT(std::ranges::is_sorted(points));
    prealloc_points_.clear();
    prealloc_points_.reserve(size(points));
    if (incoming_sum) {
        *incoming_sum = 0;
    }
    for (T const t : points) {
        if (incoming_sum) {
            *incoming_sum += t;
        }
        prealloc_points_.emplace_back(static_cast<double>(t), 1);
    }
    merge_centroids(prealloc_points_, size(points));
}

/// Print an interpolated quantile when we have all data in the series using
/// Hyndman and Fan Type 7 quantile estimation
double compute_quantile_sorted(std::span<double const>, double q);

/// Print a line of column headers for displaying quantile data
/// (e.g., MIN   5%    10%, ...)
void print_quantile_header(
    std::span<double const> quantiles, unsigned width, std::FILE *);
